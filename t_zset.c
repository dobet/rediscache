/*-----------------------------------------------------------------------------
 * Sorted set API
 *----------------------------------------------------------------------------*/

/* ZSETs are ordered sets using two data structures to hold the same elements
 * in order to get O(log(N)) INSERT and REMOVE operations into a sorted
 * data structure.
 *
 * The elements are added to a hash table mapping Redis objects to scores.
 * At the same time the elements are added to a skip list mapping scores
 * to Redis objects (so objects are sorted by scores in this "view").
 *
 * Note that the SDS string representing the element is the same in both
 * the hash table and skiplist in order to save memory. What we do in order
 * to manage the shared SDS string more easily is to free the SDS string
 * only in zslFreeNode(). The dictionary has no value free method set.
 * So we should always remove an element from the dictionary, and later from
 * the skiplist.
 *
 * This skiplist implementation is almost a C translation of the original
 * algorithm described by William Pugh in "Skip Lists: A Probabilistic
 * Alternative to Balanced Trees", modified in three ways:
 * a) this implementation allows for repeated scores.
 * b) the comparison is not just by key (our 'score') but by satellite data.
 * c) there is a back pointer, so it's a doubly linked list with the back
 * pointers being only at "level 1". This allows to traverse the list
 * from tail to head, useful for ZREVRANGE. */

#include <string.h>
#include <assert.h>
#include <limits.h>

#include "redis.h"
#include "commondef.h"
#include "commonfunc.h"
#include "object.h"
#include "zmalloc.h"
#include "db.h"
#include "zset.h"
#include "ziplist.h"
#include "util.h"
#include "solarisfixes.h"
#include "intset.h"  /* Compact integer set structure */
#include <math.h>

/* ------------------------ Lexicographic ranges ---------------------------- */

/*-----------------------------------------------------------------------------
 * Sorted set commands
 *----------------------------------------------------------------------------*/

/* This generic command implements both ZADD and ZINCRBY. */
static int zaddGenericCommand(redisDb *redis_db, robj *kobj, robj *items[], unsigned long items_size, int flags) {
    static char *nanerr = "resulting score is not a number (NaN)";
    robj *key = c->argv[1];
    robj *zobj;
    sds ele;
    double score = 0, *scores = NULL;
    int j, elements, ch = 0;
    int scoreidx = 0;
    /* The following vars are used in order to track what the command actually
     * did during the execution, to reply to the client and to trigger the
     * notification of keyspace change. */
    int added = 0;      /* Number of new elements added. */
    int updated = 0;    /* Number of elements with updated score. */
    int processed = 0;  /* Number of elements processed, may remain zero with
                           options like XX. */

    /* Parse options. At the end 'scoreidx' is set to the argument position
     * of the score of the first score-element pair. */
    scoreidx = 2;
    while(scoreidx < c->argc) {
        char *opt = c->argv[scoreidx]->ptr;
        if (!strcasecmp(opt,"nx")) flags |= ZADD_IN_NX;
        else if (!strcasecmp(opt,"xx")) flags |= ZADD_IN_XX;
        else if (!strcasecmp(opt,"ch")) ch = 1; /* Return num of elements added or updated. */
        else if (!strcasecmp(opt,"incr")) flags |= ZADD_IN_INCR;
        else if (!strcasecmp(opt,"gt")) flags |= ZADD_IN_GT;
        else if (!strcasecmp(opt,"lt")) flags |= ZADD_IN_LT;
        else break;
        scoreidx++;
    }

    /* Turn options into simple to check vars. */
    int incr = (flags & ZADD_INCR) != 0;
    int nx = (flags & ZADD_NX) != 0;
    int xx = (flags & ZADD_XX) != 0;
    int gt = (flags & ZADD_GT) != 0;
    int lt = (flags & ZADD_LT) != 0;
    
    /* After the options, we expect to have an even number of args, since
     * we expect any number of score-element pairs. */
    elements = c->argc-scoreidx;
    if (elements % 2 || !elements) {
        addReplyErrorObject(c,shared.syntaxerr);
        return;
    }
    elements /= 2; /* Now this holds the number of score-element pairs. */

    /* Check for incompatible options. */
    if (nx && xx) {
        addReplyError(c,
                      "XX and NX options at the same time are not compatible");
        return;
    }

    if ((gt && nx) || (lt && nx) || (gt && lt)) {
        addReplyError(c,
                      "GT, LT, and/or NX options at the same time are not compatible");
        return;
    }
    /* Note that XX is compatible with either GT or LT */

    if (incr && elements > 1) {
        addReplyError(c,
                      "INCR option supports a single increment-element pair");
        return;
    }

    /* Start parsing all the scores, we need to emit any syntax error
     * before executing additions to the sorted set, as the command should
     * either execute fully or nothing at all. */
    scores = zmalloc(sizeof(double)*elements);
    for (j = 0; j < elements; j++) {
        if (getDoubleFromObjectOrReply(c,c->argv[scoreidx+j*2],&scores[j],NULL)
            != C_OK) goto cleanup;
    }

    /* Lookup the key and create the sorted set if does not exist. */
    zobj = lookupKeyWrite(c->db,key);
    if (checkType(c,zobj,OBJ_ZSET)) goto cleanup;
    if (zobj == NULL) {
        if (xx) goto reply_to_client; /* No key + XX option: nothing to do. */
        zobj = zsetTypeCreate(elements, sdslen(c->argv[scoreidx+1]->ptr));
        dbAdd(c->db,key,zobj);
    } else {
        zsetTypeMaybeConvert(zobj, elements);
    }

    for (j = 0; j < elements; j++) {
        double newscore;
        score = scores[j];
        int retflags = 0;

        ele = c->argv[scoreidx+1+j*2]->ptr;
        int retval = zsetAdd(zobj, score, ele, flags, &retflags, &newscore);
        if (retval == 0) {
            addReplyError(c,nanerr);
            goto cleanup;
        }
        if (retflags & ZADD_OUT_ADDED) added++;
        if (retflags & ZADD_OUT_UPDATED) updated++;
        if (!(retflags & ZADD_OUT_NOP)) processed++;
        score = newscore;
    }
    server.dirty += (added+updated);

    reply_to_client:
    if (incr) { /* ZINCRBY or INCR option. */
        if (processed)
            addReplyDouble(c,score);
        else
            addReplyNull(c);
    } else { /* ZADD. */
        addReplyLongLong(c,ch ? added+updated : added);
    }

    cleanup:
    zfree(scores);
    if (added || updated) {
        signalModifiedKey(c,c->db,key);
        notifyKeyspaceEvent(NOTIFY_ZSET,
                            incr ? "zincr" : "zadd", key, c->db->id);
    }
}

typedef enum {
    ZRANGE_AUTO = 0,
    ZRANGE_RANK,
    ZRANGE_SCORE,
    ZRANGE_LEX,
} zrange_type;

/* Implements ZREMRANGEBYRANK, ZREMRANGEBYSCORE, ZREMRANGEBYLEX commands. */
void zremrangeGenericCommand(client *c, zrange_type rangetype) {
    robj *key = c->argv[1];
    robj *zobj;
    int keyremoved = 0;
    unsigned long deleted = 0;
    zrangespec range;
    zlexrangespec lexrange;
    long start, end, llen;
    char *notify_type = NULL;

    /* Step 1: Parse the range. */
    if (rangetype == ZRANGE_RANK) {
        notify_type = "zremrangebyrank";
        if ((getLongFromObjectOrReply(c,c->argv[2],&start,NULL) != C_OK) ||
            (getLongFromObjectOrReply(c,c->argv[3],&end,NULL) != C_OK))
            return;
    } else if (rangetype == ZRANGE_SCORE) {
        notify_type = "zremrangebyscore";
        if (zslParseRange(c->argv[2],c->argv[3],&range) != C_OK) {
            addReplyError(c,"min or max is not a float");
            return;
        }
    } else if (rangetype == ZRANGE_LEX) {
        notify_type = "zremrangebylex";
        if (zslParseLexRange(c->argv[2],c->argv[3],&lexrange) != C_OK) {
            addReplyError(c,"min or max not valid string range item");
            return;
        }
    } else {
        serverPanic("unknown rangetype %d", (int)rangetype);
    }

    /* Step 2: Lookup & range sanity checks if needed. */
    if ((zobj = lookupKeyWriteOrReply(c,key,shared.czero)) == NULL ||
        checkType(c,zobj,OBJ_ZSET)) goto cleanup;

    if (rangetype == ZRANGE_RANK) {
        /* Sanitize indexes. */
        llen = zsetLength(zobj);
        if (start < 0) start = llen+start;
        if (end < 0) end = llen+end;
        if (start < 0) start = 0;

        /* Invariant: start >= 0, so this test will be true when end < 0.
         * The range is empty when start > end or start >= length. */
        if (start > end || start >= llen) {
            addReply(c,shared.czero);
            goto cleanup;
        }
        if (end >= llen) end = llen-1;
    }

    /* Step 3: Perform the range deletion operation. */
    if (zobj->encoding == OBJ_ENCODING_LISTPACK) {
        switch(rangetype) {
            case ZRANGE_AUTO:
            case ZRANGE_RANK:
                zobj->ptr = zzlDeleteRangeByRank(zobj->ptr,start+1,end+1,&deleted);
                break;
            case ZRANGE_SCORE:
                zobj->ptr = zzlDeleteRangeByScore(zobj->ptr,&range,&deleted);
                break;
            case ZRANGE_LEX:
                zobj->ptr = zzlDeleteRangeByLex(zobj->ptr,&lexrange,&deleted);
                break;
        }
        if (zzlLength(zobj->ptr) == 0) {
            dbDelete(c->db,key);
            keyremoved = 1;
        }
    } else if (zobj->encoding == OBJ_ENCODING_SKIPLIST) {
        zset *zs = zobj->ptr;
        switch(rangetype) {
            case ZRANGE_AUTO:
            case ZRANGE_RANK:
                deleted = zslDeleteRangeByRank(zs->zsl,start+1,end+1,zs->dict);
                break;
            case ZRANGE_SCORE:
                deleted = zslDeleteRangeByScore(zs->zsl,&range,zs->dict);
                break;
            case ZRANGE_LEX:
                deleted = zslDeleteRangeByLex(zs->zsl,&lexrange,zs->dict);
                break;
        }
        if (htNeedsResize(zs->dict)) dictResize(zs->dict);
        if (dictSize(zs->dict) == 0) {
            dbDelete(c->db,key);
            keyremoved = 1;
        }
    } else {
        serverPanic("Unknown sorted set encoding");
    }

    /* Step 4: Notifications and reply. */
    if (deleted) {
        signalModifiedKey(c,c->db,key);
        notifyKeyspaceEvent(NOTIFY_ZSET,notify_type,key,c->db->id);
        if (keyremoved)
            notifyKeyspaceEvent(NOTIFY_GENERIC,"del",key,c->db->id);
    }
    server.dirty += deleted;
    addReplyLongLong(c,deleted);

    cleanup:
    if (rangetype == ZRANGE_LEX) zslFreeLexRange(&lexrange);
}

typedef enum {
    ZRANGE_DIRECTION_AUTO = 0,
    ZRANGE_DIRECTION_FORWARD,
    ZRANGE_DIRECTION_REVERSE
} zrange_direction;

typedef enum {
    ZRANGE_CONSUMER_TYPE_CLIENT = 0,
    ZRANGE_CONSUMER_TYPE_INTERNAL
} zrange_consumer_type;

typedef struct zrange_result_handler zrange_result_handler;

typedef void (*zrangeResultBeginFunction)(zrange_result_handler *c, long length);
typedef void (*zrangeResultFinalizeFunction)(
        zrange_result_handler *c, size_t result_count);
typedef void (*zrangeResultEmitCBufferFunction)(
        zrange_result_handler *c, const void *p, size_t len, double score);
typedef void (*zrangeResultEmitLongLongFunction)(
        zrange_result_handler *c, long long ll, double score);

void zrangeGenericCommand (zrange_result_handler *handler, int argc_start, int store,
                           zrange_type rangetype, zrange_direction direction);

/* Interface struct for ZRANGE/ZRANGESTORE generic implementation.
 * There is one implementation of this interface that sends a RESP reply to clients.
 * and one implementation that stores the range result into a zset object. */
struct zrange_result_handler {
    zrange_consumer_type                 type;
    client                              *client;
    robj                                *dstkey;
    robj                                *dstobj;
    void                                *userdata;
    int                                  withscores;
    int                                  should_emit_array_length;
    zrangeResultBeginFunction            beginResultEmission;
    zrangeResultFinalizeFunction         finalizeResultEmission;
    zrangeResultEmitCBufferFunction      emitResultFromCBuffer;
    zrangeResultEmitLongLongFunction     emitResultFromLongLong;
};

/* This command implements ZRANGEBYSCORE, ZREVRANGEBYSCORE. */
void genericZrangebyscoreCommand(zrange_result_handler *handler,
                                 zrangespec *range, robj *zobj, long offset, long limit,
                                 int reverse) {
    unsigned long rangelen = 0;

    handler->beginResultEmission(handler, -1);

    /* For invalid offset, return directly. */
    if (offset > 0 && offset >= (long)zsetLength(zobj)) {
        handler->finalizeResultEmission(handler, 0);
        return;
    }

    if (zobj->encoding == OBJ_ENCODING_LISTPACK) {
        unsigned char *zl = zobj->ptr;
        unsigned char *eptr, *sptr;
        unsigned char *vstr;
        unsigned int vlen;
        long long vlong;

        /* If reversed, get the last node in range as starting point. */
        if (reverse) {
            eptr = zzlLastInRange(zl,range);
        } else {
            eptr = zzlFirstInRange(zl,range);
        }

        /* Get score pointer for the first element. */
        if (eptr)
            sptr = lpNext(zl,eptr);

        /* If there is an offset, just traverse the number of elements without
         * checking the score because that is done in the next loop. */
        while (eptr && offset--) {
            if (reverse) {
                zzlPrev(zl,&eptr,&sptr);
            } else {
                zzlNext(zl,&eptr,&sptr);
            }
        }

        while (eptr && limit--) {
            double score = zzlGetScore(sptr);

            /* Abort when the node is no longer in range. */
            if (reverse) {
                if (!zslValueGteMin(score,range)) break;
            } else {
                if (!zslValueLteMax(score,range)) break;
            }

            vstr = lpGetValue(eptr,&vlen,&vlong);
            rangelen++;
            if (vstr == NULL) {
                handler->emitResultFromLongLong(handler, vlong, score);
            } else {
                handler->emitResultFromCBuffer(handler, vstr, vlen, score);
            }

            /* Move to next node */
            if (reverse) {
                zzlPrev(zl,&eptr,&sptr);
            } else {
                zzlNext(zl,&eptr,&sptr);
            }
        }
    } else if (zobj->encoding == OBJ_ENCODING_SKIPLIST) {
        zset *zs = zobj->ptr;
        zskiplist *zsl = zs->zsl;
        zskiplistNode *ln;

        /* If reversed, get the last node in range as starting point. */
        if (reverse) {
            ln = zslLastInRange(zsl,range);
        } else {
            ln = zslFirstInRange(zsl,range);
        }

        /* If there is an offset, just traverse the number of elements without
         * checking the score because that is done in the next loop. */
        while (ln && offset--) {
            if (reverse) {
                ln = ln->backward;
            } else {
                ln = ln->level[0].forward;
            }
        }

        while (ln && limit--) {
            /* Abort when the node is no longer in range. */
            if (reverse) {
                if (!zslValueGteMin(ln->score,range)) break;
            } else {
                if (!zslValueLteMax(ln->score,range)) break;
            }

            rangelen++;
            handler->emitResultFromCBuffer(handler, ln->ele, sdslen(ln->ele), ln->score);

            /* Move to next node */
            if (reverse) {
                ln = ln->backward;
            } else {
                ln = ln->level[0].forward;
            }
        }
    } else {
        serverPanic("Unknown sorted set encoding");
    }

    handler->finalizeResultEmission(handler, rangelen);
}

/* ZRANGEBYSCORE <key> <min> <max> [WITHSCORES] [LIMIT offset count] */
void zrangebyscoreCommand(client *c) {
    zrange_result_handler handler;
    zrangeResultHandlerInit(&handler, c, ZRANGE_CONSUMER_TYPE_CLIENT);
    zrangeGenericCommand(&handler, 1, 0, ZRANGE_SCORE, ZRANGE_DIRECTION_FORWARD);
}


/* This command implements ZRANGEBYLEX, ZREVRANGEBYLEX. */
void genericZrangebylexCommand(zrange_result_handler *handler,
                               zlexrangespec *range, robj *zobj, int withscores, long offset, long limit,
                               int reverse)
{
    unsigned long rangelen = 0;

    handler->beginResultEmission(handler, -1);

    if (zobj->encoding == OBJ_ENCODING_LISTPACK) {
        unsigned char *zl = zobj->ptr;
        unsigned char *eptr, *sptr;
        unsigned char *vstr;
        unsigned int vlen;
        long long vlong;

        /* If reversed, get the last node in range as starting point. */
        if (reverse) {
            eptr = zzlLastInLexRange(zl,range);
        } else {
            eptr = zzlFirstInLexRange(zl,range);
        }

        /* Get score pointer for the first element. */
        if (eptr)
            sptr = lpNext(zl,eptr);

        /* If there is an offset, just traverse the number of elements without
         * checking the score because that is done in the next loop. */
        while (eptr && offset--) {
            if (reverse) {
                zzlPrev(zl,&eptr,&sptr);
            } else {
                zzlNext(zl,&eptr,&sptr);
            }
        }

        while (eptr && limit--) {
            double score = 0;
            if (withscores) /* don't bother to extract the score if it's gonna be ignored. */
                score = zzlGetScore(sptr);

            /* Abort when the node is no longer in range. */
            if (reverse) {
                if (!zzlLexValueGteMin(eptr,range)) break;
            } else {
                if (!zzlLexValueLteMax(eptr,range)) break;
            }

            vstr = lpGetValue(eptr,&vlen,&vlong);
            rangelen++;
            if (vstr == NULL) {
                handler->emitResultFromLongLong(handler, vlong, score);
            } else {
                handler->emitResultFromCBuffer(handler, vstr, vlen, score);
            }

            /* Move to next node */
            if (reverse) {
                zzlPrev(zl,&eptr,&sptr);
            } else {
                zzlNext(zl,&eptr,&sptr);
            }
        }
    } else if (zobj->encoding == OBJ_ENCODING_SKIPLIST) {
        zset *zs = zobj->ptr;
        zskiplist *zsl = zs->zsl;
        zskiplistNode *ln;

        /* If reversed, get the last node in range as starting point. */
        if (reverse) {
            ln = zslLastInLexRange(zsl,range);
        } else {
            ln = zslFirstInLexRange(zsl,range);
        }

        /* If there is an offset, just traverse the number of elements without
         * checking the score because that is done in the next loop. */
        while (ln && offset--) {
            if (reverse) {
                ln = ln->backward;
            } else {
                ln = ln->level[0].forward;
            }
        }

        while (ln && limit--) {
            /* Abort when the node is no longer in range. */
            if (reverse) {
                if (!zslLexValueGteMin(ln->ele,range)) break;
            } else {
                if (!zslLexValueLteMax(ln->ele,range)) break;
            }

            rangelen++;
            handler->emitResultFromCBuffer(handler, ln->ele, sdslen(ln->ele), ln->score);

            /* Move to next node */
            if (reverse) {
                ln = ln->backward;
            } else {
                ln = ln->level[0].forward;
            }
        }
    } else {
        serverPanic("Unknown sorted set encoding");
    }

    handler->finalizeResultEmission(handler, rangelen);
}

/**
 * This function handles ZRANGE and ZRANGESTORE, and also the deprecated
 * Z[REV]RANGE[BYSCORE|BYLEX] commands.
 *
 * The simple ZRANGE and ZRANGESTORE can take _AUTO in rangetype and direction,
 * other command pass explicit value.
 *
 * The argc_start points to the src key argument, so following syntax is like:
 * <src> <min> <max> [BYSCORE | BYLEX] [REV] [WITHSCORES] [LIMIT offset count]
 */
void zrangeGenericCommand(zrange_result_handler *handler, int argc_start, int store,
                          zrange_type rangetype, zrange_direction direction)
{
    client *c = handler->client;
    robj *key = c->argv[argc_start];
    robj *zobj;
    zrangespec range;
    zlexrangespec lexrange;
    int minidx = argc_start + 1;
    int maxidx = argc_start + 2;

    /* Options common to all */
    long opt_start = 0;
    long opt_end = 0;
    int opt_withscores = 0;
    long opt_offset = 0;
    long opt_limit = -1;

    /* Step 1: Skip the <src> <min> <max> args and parse remaining optional arguments. */
    for (int j=argc_start + 3; j < c->argc; j++) {
        int leftargs = c->argc-j-1;
        if (!store && !strcasecmp(c->argv[j]->ptr,"withscores")) {
            opt_withscores = 1;
        } else if (!strcasecmp(c->argv[j]->ptr,"limit") && leftargs >= 2) {
            if ((getLongFromObjectOrReply(c, c->argv[j+1], &opt_offset, NULL) != C_OK) ||
                (getLongFromObjectOrReply(c, c->argv[j+2], &opt_limit, NULL) != C_OK))
            {
                return;
            }
            j += 2;
        } else if (direction == ZRANGE_DIRECTION_AUTO &&
                   !strcasecmp(c->argv[j]->ptr,"rev"))
        {
            direction = ZRANGE_DIRECTION_REVERSE;
        } else if (rangetype == ZRANGE_AUTO &&
                   !strcasecmp(c->argv[j]->ptr,"bylex"))
        {
            rangetype = ZRANGE_LEX;
        } else if (rangetype == ZRANGE_AUTO &&
                   !strcasecmp(c->argv[j]->ptr,"byscore"))
        {
            rangetype = ZRANGE_SCORE;
        } else {
            addReplyErrorObject(c,shared.syntaxerr);
            return;
        }
    }

    /* Use defaults if not overridden by arguments. */
    if (direction == ZRANGE_DIRECTION_AUTO)
        direction = ZRANGE_DIRECTION_FORWARD;
    if (rangetype == ZRANGE_AUTO)
        rangetype = ZRANGE_RANK;

    /* Check for conflicting arguments. */
    if (opt_limit != -1 && rangetype == ZRANGE_RANK) {
        addReplyError(c,"syntax error, LIMIT is only supported in combination with either BYSCORE or BYLEX");
        return;
    }
    if (opt_withscores && rangetype == ZRANGE_LEX) {
        addReplyError(c,"syntax error, WITHSCORES not supported in combination with BYLEX");
        return;
    }

    if (direction == ZRANGE_DIRECTION_REVERSE &&
        ((ZRANGE_SCORE == rangetype) || (ZRANGE_LEX == rangetype)))
    {
        /* Range is given as [max,min] */
        int tmp = maxidx;
        maxidx = minidx;
        minidx = tmp;
    }

    /* Step 2: Parse the range. */
    switch (rangetype) {
        case ZRANGE_AUTO:
        case ZRANGE_RANK:
            /* Z[REV]RANGE, ZRANGESTORE [REV]RANGE */
            if ((getLongFromObjectOrReply(c, c->argv[minidx], &opt_start,NULL) != C_OK) ||
                (getLongFromObjectOrReply(c, c->argv[maxidx], &opt_end,NULL) != C_OK))
            {
                return;
            }
            break;

        case ZRANGE_SCORE:
            /* Z[REV]RANGEBYSCORE, ZRANGESTORE [REV]RANGEBYSCORE */
            if (zslParseRange(c->argv[minidx], c->argv[maxidx], &range) != C_OK) {
                addReplyError(c, "min or max is not a float");
                return;
            }
            break;

        case ZRANGE_LEX:
            /* Z[REV]RANGEBYLEX, ZRANGESTORE [REV]RANGEBYLEX */
            if (zslParseLexRange(c->argv[minidx], c->argv[maxidx], &lexrange) != C_OK) {
                addReplyError(c, "min or max not valid string range item");
                return;
            }
            break;
    }

    if (opt_withscores || store) {
        zrangeResultHandlerScoreEmissionEnable(handler);
    }

    /* Step 3: Lookup the key and get the range. */
    zobj = lookupKeyRead(c->db, key);
    if (zobj == NULL) {
        if (store) {
            handler->beginResultEmission(handler, -1);
            handler->finalizeResultEmission(handler, 0);
        } else {
            addReply(c, shared.emptyarray);
        }
        goto cleanup;
    }

    if (checkType(c,zobj,OBJ_ZSET)) goto cleanup;

    /* Step 4: Pass this to the command-specific handler. */
    switch (rangetype) {
        case ZRANGE_AUTO:
        case ZRANGE_RANK:
            genericZrangebyrankCommand(handler, zobj, opt_start, opt_end,
                                       opt_withscores || store, direction == ZRANGE_DIRECTION_REVERSE);
            break;

        case ZRANGE_SCORE:
            genericZrangebyscoreCommand(handler, &range, zobj, opt_offset,
                                        opt_limit, direction == ZRANGE_DIRECTION_REVERSE);
            break;

        case ZRANGE_LEX:
            genericZrangebylexCommand(handler, &lexrange, zobj, opt_withscores || store,
                                      opt_offset, opt_limit, direction == ZRANGE_DIRECTION_REVERSE);
            break;
    }

    /* Instead of returning here, we'll just fall-through the clean-up. */

    cleanup:

    if (rangetype == ZRANGE_LEX) {
        zslFreeLexRange(&lexrange);
    }
}

void zrankGenericCommand(client *c, int reverse) {
    robj *key = c->argv[1];
    robj *ele = c->argv[2];
    robj *zobj;
    robj* reply;
    long rank;
    int opt_withscore = 0;
    double score;

    if (c->argc > 4) {
        addReplyErrorArity(c);
        return;
    }
    if (c->argc > 3) {
        if (!strcasecmp(c->argv[3]->ptr, "withscore")) {
            opt_withscore = 1;
        } else {
            addReplyErrorObject(c, shared.syntaxerr);
            return;
        }
    }
    reply = opt_withscore ? shared.nullarray[c->resp] : shared.null[c->resp];
    if ((zobj = lookupKeyReadOrReply(c, key, reply)) == NULL || checkType(c, zobj, OBJ_ZSET)) {
        return;
    }
    serverAssertWithInfo(c, ele, sdsEncodedObject(ele));
    rank = zsetRank(zobj, ele->ptr, reverse, opt_withscore ? &score : NULL);
    if (rank >= 0) {
        if (opt_withscore) {
            addReplyArrayLen(c, 2);
        }
        addReplyLongLong(c, rank);
        if (opt_withscore) {
            addReplyDouble(c, score);
        }
    } else {
        if (opt_withscore) {
            addReplyNullArray(c);
        } else {
            addReplyNull(c);
        }
    }
}

int RcZCount(redisCache db, robj *key, robj *min, robj *max, unsigned long *len)
{
    if (NULL == db || NULL == key || NULL == min || NULL == max) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    robj *zobj;
    if ((zobj = lookupKeyRead(redis_db,key)) == NULL || checkType(zobj,OBJ_ZSET)) {
        return REDIS_KEY_NOT_EXIST;
    }

    /* Parse the range arguments */
    zrangespec range;
    if (zslParseRange(min,max,&range) != C_OK) {
        return C_ERR;
    }

    unsigned long count = 0;
    if (zobj->encoding == OBJ_ENCODING_ZIPLIST) {
        unsigned char *zl = zobj->ptr;
        unsigned char *eptr, *sptr;
        double score;

        /* Use the first element in range as the starting point */
        eptr = zzlFirstInRange(zl,&range);

        /* No "first" element */
        if (eptr == NULL) {
            *len = 0;
            return C_OK;
        }

        /* First element is in range */
        sptr = ziplistNext(zl,eptr);
        score = zzlGetScore(sptr);
        assert(zslValueLteMax(score,&range));

        /* Iterate over elements in range */
        while (eptr) {
            score = zzlGetScore(sptr);

            /* Abort when the node is no longer in range. */
            if (!zslValueLteMax(score,&range)) {
                break;
            } else {
                count++;
                zzlNext(zl,&eptr,&sptr);
            }
        }
    } else if (zobj->encoding == OBJ_ENCODING_SKIPLIST) {
        zset *zs = zobj->ptr;
        zskiplist *zsl = zs->zsl;
        zskiplistNode *zn;
        unsigned long rank;

        /* Find first element in range */
        zn = zslFirstInRange(zsl, &range);

        /* Use rank of first element, if any, to determine preliminary count */
        if (zn != NULL) {
            rank = zslGetRank(zsl, zn->score, zn->ele);
            count = (zsl->length - (rank - 1));

            /* Find last element in range */
            zn = zslLastInRange(zsl, &range);

            /* Use rank of last element, if any, to determine the actual count */
            if (zn != NULL) {
                rank = zslGetRank(zsl, zn->score, zn->ele);
                count -= (zsl->length - rank);
            }
        }
    } else {
        return C_ERR;
    }

    *len = count;

    return C_OK;
}

int RcZIncrby(redisCache db, robj *key, robj *items[], unsigned long items_size)
{
    if (NULL == db || NULL == key || NULL == items) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    return zaddGenericCommand(redis_db, key, items, items_size, ZADD_INCR);
}

int RcZrange(redisCache db, robj *key, long start, long end, zitem **items, unsigned long *items_size)
{
    if (NULL == db || NULL == key) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    return zrangeGenericCommand(redis_db, key, start, end, items, items_size, 0);
}

int RcZRangebyscore(redisCache db, robj *key,
                    robj *min, robj *max,
                    zitem **items, unsigned long *items_size,
                    long offset, long count)
{
    if (NULL == db || NULL == key || NULL == min || NULL == max) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    return genericZrangebyscoreCommand(redis_db, key, min, max, items, items_size, 0, offset, count);
}

int RcZRank(redisCache db, robj *key, robj *member, long *rank)
{
    if (NULL == db || NULL == key || NULL == member) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    return zrankGenericCommand(redis_db, key, member, rank, 0);
}

int RcZRem(redisCache db, robj *key, robj *members[], unsigned long members_size)
{
    if (NULL == db || NULL == key || NULL == members) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    robj *zobj;
    if ((zobj = lookupKeyWrite(redis_db,key)) == NULL || checkType(zobj,OBJ_ZSET)) {
        return REDIS_KEY_NOT_EXIST;
    }

    unsigned long i = 0;
    for (i = 0; i < members_size; i++) {
        zsetDel(zobj,members[i]->ptr);
        if (zsetLength(zobj) == 0) {
            dbDelete(redis_db,key);
            break;
        }
    }

    return C_OK;
}

int RcZRemrangebyrank(redisCache db, robj *key, robj *min, robj *max)
{
    if (NULL == db || NULL == key) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    return zremrangeGenericCommand(redis_db, key, min, max, ZRANGE_RANK);
}

int RcZRemrangebyscore(redisCache db, robj *key, robj *min, robj *max)
{
    if (NULL == db || NULL == key) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    return zremrangeGenericCommand(redis_db, key, min, max, ZRANGE_SCORE);
}

int RcZRevrange(redisCache db, robj *key,
                long start, long end,
                zitem **items, unsigned long *items_size)
{
    if (NULL == db || NULL == key) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    return zrangeGenericCommand(redis_db, key, start, end, items, items_size, 1);
}

int RcZRevrangebyscore(redisCache db, robj *key,
                       robj *min, robj *max,
                       zitem **items, unsigned long *items_size,
                       long offset, long count)
{
    if (NULL == db || NULL == key) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    return genericZrangebyscoreCommand(redis_db, key, min, max, items, items_size, 1, offset, count);
}

int RcZRevrangebylex(redisCache db, robj *key,
                     robj *min, robj *max,
                     sds **members, unsigned long *members_size)
{
    if (NULL == db || NULL == key || NULL == min || NULL == max) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    return genericZrangebylexCommand(redis_db, key, min, max, members, members_size, 1);
}

int RcZRevrank(redisCache db, robj *key, robj *member, long *rank)
{
    if (NULL == db || NULL == key || NULL == member) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    return zrankGenericCommand(redis_db, key, member, rank, 1);
}

int RcZScore(redisCache db, robj *key, robj *member, double *score)
{
    if (NULL == db || NULL == key || NULL == member) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    robj *zobj;
    if ((zobj = lookupKeyRead(redis_db,key)) == NULL || checkType(zobj,OBJ_ZSET)) {
        return REDIS_KEY_NOT_EXIST;
    }

    if (zsetScore(zobj,member->ptr,score) == C_ERR) {
        return REDIS_ITEM_NOT_EXIST;
    }

    return C_OK;
}

int RcZRangebylex(redisCache db, robj *key,
                  robj *min, robj *max,
                  sds **members, unsigned long *members_size)
{
    if (NULL == db || NULL == key || NULL == min || NULL == max) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    return genericZrangebylexCommand(redis_db, key, min, max, members, members_size, 0);
}

int RcZLexcount(redisCache db, robj *key, robj *min, robj *max, unsigned long *len)
{
    if (NULL == db || NULL == key || NULL == min || NULL == max) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    robj *zobj;
    if ((zobj = lookupKeyRead(redis_db,key)) == NULL || checkType(zobj,OBJ_ZSET)) {
        return REDIS_KEY_NOT_EXIST;
    }

    /* Parse the range arguments */
    zlexrangespec range;
    if (zslParseLexRange(min,max,&range) != C_OK) {
        return C_ERR;
    }

    int count = 0;
    if (zobj->encoding == OBJ_ENCODING_ZIPLIST) {
        unsigned char *zl = zobj->ptr;
        unsigned char *eptr, *sptr;

        /* Use the first element in range as the starting point */
        eptr = zzlFirstInLexRange(zl,&range);

        /* No "first" element */
        if (eptr == NULL) {
            *len = 0;
            zslFreeLexRange(&range);
            return C_OK;
        }

        /* First element is in range */
        sptr = ziplistNext(zl,eptr);
        assert(zzlLexValueLteMax(eptr,&range));

        /* Iterate over elements in range */
        while (eptr) {
            /* Abort when the node is no longer in range. */
            if (!zzlLexValueLteMax(eptr,&range)) {
                break;
            } else {
                count++;
                zzlNext(zl,&eptr,&sptr);
            }
        }
    } else if (zobj->encoding == OBJ_ENCODING_SKIPLIST) {
        zset *zs = zobj->ptr;
        zskiplist *zsl = zs->zsl;
        zskiplistNode *zn;
        unsigned long rank;

        /* Find first element in range */
        zn = zslFirstInLexRange(zsl, &range);

        /* Use rank of first element, if any, to determine preliminary count */
        if (zn != NULL) {
            rank = zslGetRank(zsl, zn->score, zn->ele);
            count = (zsl->length - (rank - 1));

            /* Find last element in range */
            zn = zslLastInLexRange(zsl, &range);

            /* Use rank of last element, if any, to determine the actual count */
            if (zn != NULL) {
                rank = zslGetRank(zsl, zn->score, zn->ele);
                count -= (zsl->length - rank);
            }
        }
    } else {
        zslFreeLexRange(&range);
        return C_ERR;
    }

    *len = count;

    zslFreeLexRange(&range);
    return C_OK;
}

int RcZRemrangebylex(redisCache db, robj *key, robj *min, robj *max)
{
    if (NULL == db || NULL == key) {
        return REDIS_INVALID_ARG;
    }
    redisDb *redis_db = (redisDb*)db;

    return zremrangeGenericCommand(redis_db, key, min, max, ZRANGE_LEX);
}