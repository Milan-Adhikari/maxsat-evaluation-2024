#include "Solver.h"
#include "../mtl/Sort.h"

inline Lit Solver::subsume(const Clause &c, const Clause &d)
{
    if ((c.size() > d.size()) || ((c.abstraction() & ~d.abstraction()) != 0))
        return lit_Error;
    Lit ret = lit_Undef;

    allsbsm++;
    counter++;
    for (int i = 0; i < d.size(); i++)
        seen2[toInt(d[i])] = counter;

    for (int i = 0; i < c.size(); i++)
    {
        if (seen2[toInt(~c[i])] == counter)
        {
            if (ret == lit_Undef)
                ret = c[i];
            else
            {
                sbsmTtlg++;
                if (d.size() == 2)
                {
                    assert(c.size() == 2);
                    Lit p = getRpr(d[0]);
                    Lit q = getRpr(d[1]);
                    if (var(p) != var(q) && (!dynVar(var(p)) && !dynVar(var(q))))
                    {
                        if (isSoftLits(var(p)) && isSoftLits(var(q)))
                        {
                            if (weights[var(q)] > weights[var(p)])
                            {
                                Lit r = p;
                                p = q;
                                q = r;
                            }
                        }
                        else if (isSoftLits(var(q)) && !isSoftLits(var(p)))
                        {
                            Lit r = p;
                            p = q;
                            q = r;
                        }
                        if (dynVar(var(p)) && !dynVar(var(q)))
                        {
                            Lit r = p;
                            p = q;
                            q = r;
                        }

                        smeq++;
                        feasibleNbEq++;
                        rpr[toInt(q)] = ~p;
                        rpr[toInt(~q)] = p;
                        if (isSoftLits(var(p)) && isSoftLits(var(q)))
                            nbSoftEq++;
                        equivLits.push(q);
                    }
                }
                return lit_Error;
            }
        }
        else if (seen2[toInt(c[i])] != counter)
        {
            sbsmAbsFail++;
            return lit_Error;
        }
    }
    return ret;
}

bool Solver::subsumeClauses(CRef cr, int &subsumed, int &deleted_literals)
{
    Clause &c = ca[cr];
    assert(c.size() > 1 || value(c[0]) == l_True); // Unit-clauses should have been propagated before this point.
    // Find best variable to scan:
    Var best = var(c[0]);
    for (int i = 1; i < c.size(); i++)
        if (occurIn[var(c[i])].size() < occurIn[best].size())
            best = var(c[i]);

    // Search all candidates:
    vec<CRef> &_cs = occurIn.lookup(best);
    CRef *cs = (CRef *)_cs;
    for (int j = 0; j < _cs.size(); j++)
    {
        assert(!removed(cr));
        CRef dr = cs[j];
        if (dr != cr && !removed(dr))
        {
            Clause &d = ca[dr];
            Lit l = subsume(c, d); // c.subsumes(d);
            if (l == lit_Undef)
            {
                if (c.learnt() && !d.learnt())
                {
                    if (c.size() < d.size())
                    {
                        nbOriClsLits -= (d.size() - c.size());
                        detachClause(dr, true);
                        removeClauseFromOccur(dr, true);
                        for (int k = 0; k < c.size(); k++)
                        {
                            d[k] = c[k];
                            vec<CRef> &cls = occurIn[var(d[k])];
                            int m;
                            for (m = 0; m < cls.size(); m++)
                                if (cls[m] == cr)
                                {
                                    cls[m] = dr;
                                    break;
                                }
                            assert(m < cls.size());
                        }
                        d.shrink(d.size() - c.size());
                        d.setAbs(c.abstraction());
                        d.setSimplified(c.simplified());
                        d.set_lbd(c.lbd());
                        d.setLastPoint(c.lastPoint());
                        attachClause(dr);
                    }
                    else
                        removeClauseFromOccur(cr);
                    subsumed++;
                    removeClause(cr);
                    subsumptionQueue.push(dr);
                    return true;
                }
                else
                {
                    if (!d.learnt())
                        nbOriClsLits -= d.size();
                    subsumed++, removeClause(dr);
                    removeClauseFromOccur(dr);
                }
                // if (c.learnt() && !d.learnt()) {
                //   c.promote();
                //   clauses.push(cr);
                // }
                // subsumed++, removeClause(dr); removeClauseFromOccur(dr);
            }
            else if (l != lit_Error)
            {
                if (!d.learnt())
                    nbOriClsLits--;
                deleted_literals++;
                if (!simpleStrengthenClause(dr, ~l))
                    return false;
                // Did current candidate get deleted from cs? Then check candidate at index j again:
                if (var(l) == best)
                    j--;
            }
        }
    }
    return true;
}

#define sbsmFailLimit 5000000

struct clauseSize_lt
{
    ClauseAllocator &ca;
    clauseSize_lt(ClauseAllocator &ca_) : ca(ca_) {}
    bool operator()(CRef x, CRef y)
    {

        return ca[x].size() < ca[y].size();
    }
};

bool Solver::backwardSubsume()
{
    int savedTrail = trail.size(); // savedOriginal;
    int subsumed = 0, deleted_literals = 0;

#ifdef printBackWardSubsumeData
    int nbSubsumes = 0;
    uint64_t sbsmTtlg0 = sbsmTtlg, sbsmAbsFail0 = sbsmAbsFail, allsbsm0 = allsbsm, smeq0 = smeq;
    double sbsmTime = cpuTime();
    int mySavedTrail = trail.size();
#endif
    uint64_t mysbsmAbsFail0 = sbsmAbsFail;

    subsumptionQueue.clear();
    //  int nv = cardinalityC.size() > 0 ? nVars() : staticNbVars;
    occurIn.init(nVars());
    for (int i = 0; i < nVars(); i++)
        occurIn[i].clear();

#ifdef printBackWardSubsumeData
    printf("c original clauses %d, learnts_core %d, learnts_tier2 %d, learnts_local %d\n",
           clauses.size(), learnts_core.size(), learnts_tier2.size(), learnts_local.size());
#endif
    collectClauses(clauses);

    if (clauses.size() > 1000000)
    {
        subsumptionQueue.clear();
        if (clauses.size() < 10000000)
            for (int i = 0; i < clauses.size(); i++)
            {
                CRef cr = clauses[i];
                if (ca[cr].size() == 2)
                    subsumptionQueue.push(cr);
            }
    }

    collectClauses(learnts_core, CORE);
    collectClauses(learnts_tier2, TIER2);
    collectClauses(PBC, CORE);
    //  collectClauses(learnts_local, LOCAL);
    //  savedOriginal = clauses.size();

    sort(subsumptionQueue, clauseSize_lt(ca));
    int initQueueSize = subsumptionQueue.size();
    assert(decisionLevel() == 0);
    while (subsumptionQueue.size() > 0 || savedTrail < trail.size())
    {
        // Check top-level assignments by creating a dummy clause and placing it in the queue:
        if (subsumptionQueue.size() == 0 && savedTrail < trail.size())
        {
            Lit l = trail[savedTrail++];
            ca[bwdsub_tmpunit][0] = l;
            ca[bwdsub_tmpunit].calcAbstraction();
            // subsumptionQueue.insert(bwdsub_tmpunit);
            subsumptionQueue.push(bwdsub_tmpunit);
        }

        for (int i = 0; i < subsumptionQueue.size(); i++)
        {
            if (i == initQueueSize)
            {
#ifdef printBackWardSubsumeData
                printf("c initQueue %d, %d subsumed, %d deleted literals, %d fixed vars (%d)\n", initQueueSize, subsumed, deleted_literals, trail.size() - mySavedTrail, trail.size());
                //	mySavedTrail=trail.size();
                printf("c subsumption queue grows to %d\n", subsumptionQueue.size());
#endif
                initQueueSize = subsumptionQueue.size();
                int j, k;
                for (j = 0, k = i; k < subsumptionQueue.size(); k++)
                    subsumptionQueue[j++] = subsumptionQueue[k];
                subsumptionQueue.shrink(k - j);
                i = -1;
                continue;
            }

            CRef cr = subsumptionQueue[i]; // subsumptionQueue.peek(); subsumptionQueue.pop();
            if (removed(cr))
                continue;
#ifdef printBackWardSubsumeData
            nbSubsumes++;
#endif
            if (!subsumeClauses(cr, subsumed, deleted_literals))
            {
                printf("c a conflict is found during backwardSubsumptionCheck\n");
                occurIn.cleanAll();
                return false;
            }
            if (sbsmAbsFail - mysbsmAbsFail0 > sbsmFailLimit)
                break;
        }
        subsumptionQueue.clear();
        mysbsmAbsFail0 = sbsmFailLimit;
    }

#ifdef printBackWardSubsumeData
    printf("c %d subsumptions, %5d subsumed, %5d deleted literals, %5d fixed vars\n", nbSubsumes, subsumed, deleted_literals, trail.size() - mySavedTrail);
#endif
    occurIn.cleanAll();

#ifdef printBackWardSubsumeData
    float rate1, rate2;
    if (allsbsm == allsbsm0)
    {
        rate1 = 0;
        rate2 = 0;
    }
    else
    {
        rate1 = (float)(sbsmTtlg - sbsmTtlg0) / (allsbsm - allsbsm0);
        rate2 = (float)(sbsmAbsFail - sbsmAbsFail0) / (allsbsm - allsbsm0);
    }
    printf("c allsbsm %" PRIu64 "(%" PRIu64 "), sbsmTtlg %" PRIu64 "(%" PRIu64 ", %5.4f), sbsmAbsFail %" PRIu64 "(%" PRIu64 ", %5.4f), smeq %" PRIu64 "(%" PRIu64 ")\n",
           allsbsm - allsbsm0, allsbsm, sbsmTtlg - sbsmTtlg0, sbsmTtlg, rate1,
           sbsmAbsFail - sbsmAbsFail0, sbsmAbsFail, rate2, smeq - smeq0, smeq);
    double thissbsmtime = cpuTime() - sbsmTime;
    printf("c sbsmTime %5.2lfs\n", thissbsmtime);
    totalsbsmTime += thissbsmtime;
#endif

    return true;
}

bool Solver::backwardSubsumeAndEliminateEqLits()
{
    if (!backwardSubsume())
        return false;

    if (equivLits.size() > prevEquivLitsNb)
    {
        printf("c original clauses %d, learnts_core %d, learnts_tier2 %d, learnts_local %d\n",
               clauses.size(), learnts_core.size(), learnts_tier2.size(), learnts_local.size());
        if (!eliminateEqLits())
            return false;
    }
    return true;
}