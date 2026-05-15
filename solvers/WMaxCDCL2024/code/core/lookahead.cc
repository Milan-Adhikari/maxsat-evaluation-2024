#include "Solver.h"
#include "PrintFlags.h"
#include "utils/System.h"

void Solver::setConflictForRestart(int &nbIsets)
{
    // Not used, to implement if needed
    assert(0);
}

void Solver::resetConflictsForRestart(int nbIsets, bool clearConflLits, bool pushConflLit)
{
    // Not used, to implement if needed
    assert(0);
}

int Solver::lookaheadForRestart()
{
    // Not used, to implement if needed
    assert(0);
    return 0;
}

int64_t Solver::lookaheadComputeInitLB()
{
    // Not used, to implement if needed
    assert(0);
    return rootConflCost;
}

void Solver::cancelUntilTrailRecordFillHeap()
{
    for (int i = trailRecord; i < trail.size(); i++)
    {
        Var v = var(trail[i]);
        assigns[v] = l_Undef;
        if (isSoftLits(v))
        {
            activityLB[v] = (1 - stepSizeLB) * activityLB[v];
            insertSoftLitOrder(v);
            orderHeapLookahead.decrease(v);
        }
    }
    qhead = trailRecord;
    resetTrailRecord();
}

Var Solver::pickLookaheadVar()
{
    Var v = var_Undef;
    while (lastConflLits.size() > 0)
    {
        Lit p = lastConflLits[lastConflLits.size() - 1];
        lastConflLits.shrink_(1);
        if (weights[var(p)] > 0)
            assert(isSoftLits(var(p)));
        if (value(p) == l_Undef && weights[var(p)] > 0)
            return var(p);
    }
    while (!orderHeapLookahead.empty())
    {
        v = orderHeapLookahead.removeMin();
        assert(v != var_Undef);
        if (weights[v] > 0)
            assert(isSoftLits(v));
        if (value(v) == l_Undef && weights[v] > 0)
            return v;
    }
    return var_Undef;
}

bool Solver::enqueueAssumptions(int &nextIdx, bool recheckNext)
{
    bool someEnqueued = false;
    if (recheckNext)
    {
        while (nextIdx < lastCores.size() && !someEnqueued)
        {
            int core = lastCores[nextIdx];
            LocalCore &c = localCores[core];
            // assert(c.softCl.size() == 0);
            bool active = true;
            for (int j = 0; j < c.coreLits.size() && active; j++)
            {
                Lit p = c.coreLits[j].lit;
                // Var v = var(p);
                if (value(p) == l_False)
                    active = false;
            }
            if (active)
            {
                for (int j = 0; j < c.coreLits.size(); j++)
                {
                    Lit p = c.coreLits[j].lit;
                    Var v = var(p);
                    if (value(v) == l_Undef && weights[v] > 0)
                    {
                        uncheckedEnqueueForLK(p);
                        someEnqueued = true;
                    }
                }
            }
            else
            {
                for (int j = 0; j < c.coreLits.size(); j++)
                    if (value(c.coreLits[j].lit) == l_Undef && weights[var(c.coreLits[j].lit)] > 0)
                        lastConflLits.push(c.coreLits[j].lit);
            }

            nextIdx++;
        }

        if (someEnqueued)
            return true;
        if (activeCores.size() > 0)
        {
            vec<coreLit> &coreLits = localCores[activeCores.last()].coreLits;
            for (int i = coreLits.size() - 1; i >= 0; i--)
            {
                if (nonLockedVar(var(coreLits[i].lit)) && value(coreLits[i].lit) == l_Undef)
                {
                    uncheckedEnqueueForLK(coreLits[i].lit);
                    someEnqueued = true;
                }
            }
        }
    }

    if (someEnqueued)
        return true;

    Var v = pickLookaheadVar();
    if (v == var_Undef)
        return false;

    assert(nonLockedVar(v));
    uncheckedEnqueueForLK(softLits[v]);
    return true;
}

void Solver::moreLookahead()
{
    resetCoresData();
    vec<Lit> out_learnt;
    UBconflictFlag = false;
    softConflictFlag = false;
    falseVar = var_Undef;
    falseCore = core_Undef;
    // bool foundCores = false;
    bool recheckNext = true;
    bool maxResDone = false;
    int nextIdx = 0;

    while (countedWeight + laConflictCost < UB)
    {
        if (!enqueueAssumptions(nextIdx, recheckNext))
        {
            TodoSecondLookahead = todoSecondLookahead();
            cancelUntilTrailRecordFillHeap();
            break;
        }
        recheckNext = false;

        CRef confl = propagateForLK(true);
        if (confl != CRef_Undef || falseVar != var_Undef)
        {
            assert(falseVar == var_Undef || reason(falseVar) != CRef_Undef);
            if (confl == CRef_Undef)
                confl = reason(falseVar);

            int coreIdx = pickCoreIdx();
            int64_t coreCost; // = lookbackGetMinIsetCost(confl, falseVar);
            lookbackResetTrail(confl, falseVar, out_learnt, coreIdx, coreCost, maxResDone, UB - countedWeight - laConflictCost);
            assert(coreCost > 0);
            falseVar = var_Undef;
            recheckNext = true;
            LocalCore &core = localCores[coreIdx];
            // unlockableCore = false;

            // This case is triggered when it is discovered that a literal can be propagated at DL,
            // because only  assigning ~out_learnt[0] suffices to derive a conflicting clause
            if (core.coreLits.size() == 0) //&& core.softCl.size() == 0)
            {
                freeCores.push(coreIdx);
                resetConflicts_();
                int prevLevel = decisionLevel();
                fixByLookahead(out_learnt);
                CRef confl = lPropagate();
                if (confl != CRef_Undef || softConflictFlag)
                {
                    if (confl != CRef_Undef)
                    {
                        LHconfl = confl;
                        softConflictFlag = false;
                        UBconflictFlag = false;
                    }
                    return;
                }
                setTrailRecord();
                assert(UB > countedWeight);
                assert(laConflictCost == 0);
                assert(activeCores.size() == 0);
                lastConflLits.clear();
                maxResDone = false;
                nextIdx = 0;
                if (prevLevel > decisionLevel())
                    return;
                /*for(int i=conflLits.size()-1; i>=0; i--)
                    if  (conflLits[i] != lit_Undef)
                        lastConflLits.push(conflLits[i]);*/
            }
            else
            {
                setCore(coreIdx, coreCost);
            }
        }
    }
    if (countedWeight + laConflictCost >= UB)
    {
        assert(LHconfl == CRef_Undef);
        softConflictFlag = true;
        UBconflictFlag = true;
        nbLKsuccess++;
    }
    // printAroundSecondLookahead(true);
}

bool Solver::uncheckedEnqueueForLKMultilocks(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    Var v = var(p);
    assigns[v] = lbool(!sign(p));
    vardata[v].reason = from;
    vardata[v].level = decisionLevel() + 1;
    vardata[v].index = trail.size();
    trail.push_(p);

    if (isSoftLits(v))
    {
        if (from == CRef_Undef)
        {
            assert(softLits[v] == p);
            //LAM_PRINT(LOOKAHEAD, "  c satisfied softLit %d(%" PRId64 ") \n", toInt(p), weights[v]);
        }
        else if (softLits[v] == ~p)
        {
            LAM_PRINT(LOOKAHEAD, "  c falsified softLit %d \n", toInt(p));
            if (nonLockedVar(v)) // || unlockedVar(v))
            {
                LAM_PRINT(LOOKAHEAD, "    c find falseVar %d, lit %d, \n", v, toInt(softLits[v]));
                falseVar = v;
                falseCore = core_Undef;
                return false;
            }
            else
            {
                assert(coresOfVar[v].size() > 0 && weights[v] == 0);
                for (int i = 0; i < coresOfVar[v].size(); i++)
                {
                    int coreid = coresOfVar[v][i];
                    assert(coreid >= 0 && coreid < localCores.size());
                    LocalCore &core = localCores[coreid];
                    assert(core.falsifiedWeight <= core.weight);

                    int64_t w = getCorelitWeight(coreid, v);
                    assert(w > 0);
                    if (core.falsifiedWeight == 0)
                        affectedCores.push(coreid);
                    core.falsifiedWeight += w;
                    LAM_PRINT(LOOKAHEAD, "    c core %d falsifiedWeight inc to %" PRId64 ", core weight %" PRId64 " \n", coreid, core.falsifiedWeight, core.weight);

                    if (core.falsifiedWeight < core.weight)
                        continue;
                    if (core.unlockedIndex == -1)
                    {
                        core.unlockedIndex = trail.size();
                        for (int j = 0; j < core.coreLits.size(); j++)
                        {
                            Lit pp = core.coreLits[j].lit;
                            Var vv = var(pp);
                            if (unlockCoreOfVar[vv] == -1)
                            {
                                unlockCoreOfVar[vv] = coreid;
                                unlockedVars.push(vv);
                            }
                            if (value(pp) == l_Undef)
                                insertSoftLitOrder(vv);
                        }
                    }
                    assert(core.falsifiedWeight >= core.weight);

                    if (core.falsifiedWeight > core.weight)
                    {
                        LAM_PRINT(LOOKAHEAD, "    c find falseCore %d \n", coreid);
                        falseVar = var_Undef;
                        falseCore = coreid;
                        return false;
                    }
                }
            }
        }
    }
    return true;
}

CRef Solver::propagateForLKMultilocks()
{
    falseVar = var_Undef;
    falseCore = core_Undef;
    CRef confl = CRef_Undef;
    int num_props = 0;
    watches.cleanAll();
    watches_bin.cleanAll();
    while (qhead < trail.size())
    {
        Lit p = trail[qhead++]; // 'p' is enqueued fact to propagate.
        vec<Watcher> &ws = watches[p];
        Watcher *i, *j, *end;
        num_props++;
        // First, Propagate binary clauses
        vec<Watcher> &wbin = watches_bin[p];

        for (int k = 0; k < wbin.size(); k++)
        {
            Lit imp = wbin[k].blocker;
            if (value(imp) == l_False)
            {
                binConfl[0] = ~p;
                binConfl[1] = imp;
                return CRef_Bin;
            }
            if (value(imp) == l_Undef)
            {
                if (!uncheckedEnqueueForLKMultilocks(imp, wbin[k].cref))
                {
                    // falseVar = var(imp);
                    return CRef_Undef;
                }
            }
        }
        for (i = j = (Watcher *)ws, end = i + ws.size(); i != end;)
        {
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True)
            {
                *j++ = *i++;
                continue;
            }
            // Make sure the false literal is data[1]:
            CRef cr = i->cref;
            Clause &c = ca[cr];
            Lit false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            // If 0th watch is true, then clause is already satisfied.
            // However, 0th watch is not the blocker, make it blocker using a new watcher w
            // why not simply do i->blocker=first in this case?
            Lit first = c[0];
            //  Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True)
            {
                i->blocker = first;
                *j++ = *i++;
                continue;
            }
            assert(c.lastPoint() >= 2);
            if (c.lastPoint() > c.size())
                c.setLastPoint(2);
            for (int k = c.lastPoint(); k < c.size(); k++)
            {
                if (value(c[k]) == l_Undef)
                {
                    // watcher i is abandonned using i++, because cr watches now ~c[k] instead of p
                    // the blocker is first in the watcher. However,
                    // the blocker in the corresponding watcher in ~first is not c[1]
                    Watcher w = Watcher(cr, first);
                    i++;
                    c[1] = c[k];
                    c[k] = false_lit;
                    watches[~c[1]].push(w);
                    c.setLastPoint(k + 1);
                    goto NextClause;
                }
                else if (value(c[k]) == l_True)
                {
                    i->blocker = c[k];
                    *j++ = *i++;
                    c.setLastPoint(k);
                    goto NextClause;
                }
            }
            for (int k = 2; k < c.lastPoint(); k++)
            {
                if (value(c[k]) == l_Undef)
                {
                    // watcher i is abandonned using i++, because cr watches now ~c[k] instead of p
                    // the blocker is first in the watcher. However,
                    // the blocker in the corresponding watcher in ~first is not c[1]
                    Watcher w = Watcher(cr, first);
                    i++;
                    c[1] = c[k];
                    c[k] = false_lit;
                    watches[~c[1]].push(w);
                    c.setLastPoint(k + 1);
                    goto NextClause;
                }
                else if (value(c[k]) == l_True)
                {
                    i->blocker = c[k];
                    *j++ = *i++;
                    c.setLastPoint(k);
                    goto NextClause;
                }
            }
            // Did not find watch -- clause is unit under assignment:
            i->blocker = first;
            *j++ = *i++;
            if (value(first) == l_False)
            {
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }
            else
            {
                if (!uncheckedEnqueueForLKMultilocks(first, cr))
                {
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                    // falseVar = var(first);
                }
            }
        NextClause:;
        }
        ws.shrink(i - j);
        // if (confl == CRef_Undef)
        // 	if (shortenSoftClauses(p))
        // 	  break;
    }
    lk_propagations += num_props;
    return confl;
}

Var Solver::pickSecondLookaheadVar()
{
    Var v = var_Undef;
    while (lastConflLits.size() > 0)
    {
        Lit p = lastConflLits[lastConflLits.size() - 1];
        v = var(p);
        lastConflLits.shrink_(1);
        if (value(p) == l_Undef && (nonLockedVar(v) || unlockedVar(v)))
            return v;
    }
    while (!orderHeapLookahead.empty())
    {
        v = orderHeapLookahead.removeMin();
        assert(v != var_Undef);
        if (value(v) == l_Undef && (nonLockedVar(v) || unlockedVar(v)))
            return v;
    }
    return var_Undef;
}

bool Solver::enqueueAssumptionsMultilocks(vec<Lit> &allAssumed)
{

    while (lastAssumed.size() > 0)
    {
        Var v = var(lastAssumed.last());
        lastAssumed.pop();
        if (value(v) == l_Undef && (nonLockedVar(v) || unlockedVar(v)))
        {
            uncheckedEnqueueForLKMultilocks(softLits[v]);
            allAssumed.push(softLits[v]);
            return true;
        }
    }

    Var v = pickSecondLookaheadVar();
    if (v == var_Undef)
        return false;
    assert(nonLockedVar(v) || unlockedVar(v));
    uncheckedEnqueueForLKMultilocks(softLits[v]);
    allAssumed.push(softLits[v]);
    return true;
}

int Solver::seeUnlockLits(Var x, int falseVar)
{
    int nbfalse = 0;
    int subcoreid = unlockCoreOfVar[x];
    LocalCore &subcore = localCores[subcoreid];

    assert(subcore.falsifiedWeight >= subcore.weight);
    if (subcore.seen == true)
    {
        LAM_PRINT(LOOKAHEAD, "    Var %d, softLit %d, core %d already marked.\n", x, toInt(softLits[x]), subcoreid);
        return 0;
    }

    subcore.seen = true;
    LAM_PRINT(LOOKAHEAD, "    in seeUnlockLits, add core %d as subcore: \n", subcoreid);
    for (int i = 0; i < subcore.coreLits.size(); i++)
    {
        Var v = var(subcore.coreLits[i].lit);
        assert(level(v) > decisionLevel());
        if (v == falseVar || v == x)
            continue;
        if (!seen[v] && value(subcore.coreLits[i].lit) == l_False && trailIndex(v) <= trailIndex(x))
        {
            nbfalse++;
            seen[v] = 1;
        }
    }

    subCores.push(subcoreid);
    return nbfalse;
}

int Solver::analyzeWithClauseBin()
{
    assert(level(var(binConfl[0])) > decisionLevel());
    assert(level(var(binConfl[1])) > decisionLevel());
    seen[var(binConfl[0])] = 1;
    seen[var(binConfl[1])] = 1;
    if (VSIDS)
    {
        varBumpActivity(var(binConfl[0]), .1);
        varBumpActivity(var(binConfl[0]), .1);
    }
    return 2;
}

int Solver::analyzeWithClause(CRef confl, vec<Lit> &out_learnt, int start)
{
    int res = 0;
    Clause &c = ca[confl];
    for (int i = start; i < c.size(); i++)
    {
        Lit q = c[i];
        Var v = var(q);
        if (level(v) > 0)
        {
            // assert(!seen[v] || falseVar != var_Undef && weights[falseVar] == 0 && subCores.size() > 0);
            if (!seen[v])
            {
                seen[v] = 1;
                if (level(v) > decisionLevel())
                    res++;
                else
                {
                    // Note that involvedLits can contain lits from other isets
                    // This is not the case for out_learnt
                    out_learnt.push(q);
                    newcoreReason.push(q);
                }
                if (VSIDS)
                    varBumpActivity(v, .1);
            }
        }
    }
    return res;
}

void Solver::analyzeWithConfl(CRef confl, int &pathC, vec<Lit> &out_learnt)
{
    if (confl == CRef_Bin)
        pathC += analyzeWithClauseBin();
    else
        pathC += analyzeWithClause(confl, out_learnt, 0);
}

void Solver::analyzeWithFalsevar(int &pathC, vec<Lit> &out_learnt)
{
    newcoreLits.push(coreLit(softLits[falseVar], weights[falseVar]));
    keyAssignment.push(softLits[falseVar]);
    // LAM_PRINT(LOOKAHEAD, "push falseVar %d into new core\n", toInt(softLits[falseVar]));
    // seen[falseVar] = 1;
    CRef confl = reason(falseVar);
    Clause &c = ca[confl];
    fixBinClauseOrder(c);
    if (weights[falseVar] == 0)
        pathC += seeUnlockLits(falseVar, falseVar);
    assert(level(falseVar) > decisionLevel());
    out_learnt.push(softLits[falseVar]);
    pathC += analyzeWithClause(confl, out_learnt, 1);
}

void Solver::analyzeWithFalsecore(int &pathC, vec<Lit> &out_learnt)
{
    LocalCore &core = localCores[falseCore];
    assert(!core.seen && core.falsifiedWeight > core.weight);
    core.seen = true;
    for (int i = 0; i < core.coreLits.size(); i++)
    {
        Var v = var(core.coreLits[i].lit);
        assert(level(v) > decisionLevel());
        if (weights[v] == 0 && value(core.coreLits[i].lit) == l_False)
        {
            newcoreLits.push(coreLit(core.coreLits[i].lit, weights[v]));
            out_learnt.push(core.coreLits[i].lit);
        }
        /*else
        {
            if (!seen[v])
            {
                if (value(core.coreLits[i].lit) == l_False)
                    pathC++;
                seen[v] = 1;
            }
        }*/
    }
    subCores.push(falseCore);

    CRef confl = CRef_Undef;
    for (int i = 0; i < core.coreLits.size(); i++)
    {
        Lit p = core.coreLits[i].lit;
        Var v = var(p);
        if (value(p) == l_False && weights[v] == 0)
        {
            assert(core.coreLits[i].weight > 0);
            confl = reason(v);
            Clause &c = ca[confl];
            fixBinClauseOrder(c);
            pathC += analyzeWithClause(confl, out_learnt, 1);
        }
    }
}

void Solver::lookbackResetTrailMultilocks(CRef confl, vec<Lit> &out_learnt, bool resDone, int64_t remainingCost)
{
    lastAssumed.clear();
    int pathC = 0;
    out_learnt.clear();
    out_learnt.push();
    resDone = true;

    keyAssignment.clear();
    newcoreReason.clear();
    newcoreLits.clear();

    if (confl != CRef_Undef)
        analyzeWithConfl(confl, pathC, out_learnt);
    else if (falseVar != var_Undef)
        analyzeWithFalsevar(pathC, out_learnt);
    else
        analyzeWithFalsecore(pathC, out_learnt);

    int index = trail.size() - 1;
    while (index >= trailRecord)
    {
        Lit p = trail[index--];
        Var v = var(p);
        if (seen[v])
        {
            seen[v] = 0;
            pathC--;
            confl = reason(v);

            // We will need to keep this decrease only if confl==CRef_Undef,
            //   unless we enter the following special case, where it is accepted to use a propagated softLit (i.e. confl!=CRef_Undef)
            //   for the core in replacement

            // If UIP is reached: pathC==0.
            // And the core is empty until now: localCores[nbIsets].size() == 0
            // And
            //       is not the last iset (i.e. the one triggering the soft conflict): minIsetCost < remainingCost
            //       or the recently visited lit is soft, and therefore the unique soft lit to be included in the iset

            if (pathC == 0 && newcoreLits.size() == 0)
            {
                out_learnt[0] = ~p;
                // assigns[v] = l_Undef;
                //  If creating the unit iset will trigger the soft conflict, do it.
                //   This branch can be seen as a premature exit of the loop, since we already know that pathC==0
                //  Otherwise, we exit with an empty iset and p will be propagated by fixByLookahead
                //  Note that here p is not necessarily a manually assigned softLit for LA but can be a propagated one.
                //    In this case it acts in replacement and takes it place in the iset

                if ((nonLockedVar(v) || unlockedVar(v)) && weights[v] >= remainingCost)
                // core.coreLits.push(coreLit(p, weights[v]));
                {
                    keyAssignment.push(p);
                    newcoreLits.push(coreLit(p, weights[v]));
                }

                if (isSoftLits(v))
                    insertSoftLitOrder(v);
                break;
            }
            if (confl == CRef_Undef)
            { // Propagated soft literal for LA
                assert(nonLockedVar(v) || unlockedVar(v));
                out_learnt.push(~p);
                keyAssignment.push(p);
                newcoreLits.push(coreLit(p, weights[v]));
                LAM_PRINT(LOOKAHEAD, "c add positive assignment var %d, lit %d \n", v, toInt(p));
                if (weights[v] == 0)
                    pathC += seeUnlockLits(v, falseVar);
                else
                    lastAssumed.push(p);
            }
            else
            {
                // Undo the minimum for a softLit p s.t. reason(p)!=CRef_Undef, and therefore is not put in isets
                Clause &rc = ca[confl];
                if (!isSoftLits(v) || !hardened[v])
                    fixBinClauseOrder(rc);
                int nbSeen = 0;
                int resolventSize = pathC + out_learnt.size();
                for (int j = 1; j < rc.size(); j++)
                {
                    Lit q = rc[j];
                    Var vv = var(q);
                    if (level(vv) > 0)
                    {
                        if (seen[vv])
                            nbSeen++;
                        else
                        {
                            seen[vv] = 1;
                            if (level(vv) > decisionLevel())
                                pathC++;
                            else
                            {
                                out_learnt.push(q);
                                newcoreReason.push(q);
                            }
                            if (VSIDS)
                                varBumpActivity(vv, .1);
                        }
                    }
                }
                if (!resDone && nbSeen >= resolventSize)
                {
                    assert(falseVar == var_Undef);
                    reduceClause(confl, pathC);
                }
            }
        }
        else if (nonLockedVar(v) || unlockedVar(v))
            insertSoftLitOrder(v);
    }
    for (int i = 0; i < newcoreReason.size(); i++)
        seen[var(newcoreReason[i])] = 0;
}

/*bool Solver::todoSecondLookahead()
{
    if (activeCores.size() == 0)
    {
        LOOKAHEAD_MULTILOCKS_SKIP++;
        return false;
    }

    int64_t pruningThreshold = UB - countedWeight;
    int64_t falsifiedWeight = 0;
    //bool res = false;
    int falseLitIndex = falseLitsRecord;
    //CRef confl = CRef_Undef;
    while (falseLitIndex < falseLits.size() && falsifiedWeight <pruningThreshold)
    {
        Lit p = falseLits[falseLitIndex++];
        assert(value(p) == l_False);
        Var v = var(p);
        falsifiedWeight += weightsBckp[v];
        if (falsifiedWeight >= pruningThreshold)
            break;
        for (int i = 0; i < coresOfVar[v].size();i++)
        {
            LocalCore& core = localCores[coresOfVar[v][i]];
            for (int j = 0; j < core.coreLits.size();j++)
            {
                if (value(core.coreLits[j].lit) == l_Undef)
                    uncheckedEnqueueForLK(core.coreLits[j].lit);
            }
        }
        propagateForLK(false);
    }

    if (falsifiedWeight < pruningThreshold)
    {
        LOOKAHEAD_MULTILOCKS_SKIP++;
        return false;
    }

    // printf("\n ***** Lookahead Multilocks %" PRIu64 " Start ***** \n", LOOKAHEAD_MULTILOCKS + 1);
    // printf("c UB=%" PRId64 ", laConflictCost=%" PRId64 ", countedWeight=%" PRId64 ", rest=%" PRId64 "\n",
    //     UB, laConflictCost, countedWeight, UB - laConflictCost - countedWeight);
    // for (int i = 0;i < activeCores.size();i++)
    // {
    //     LocalCore& core = localCores[activeCores[i]];
    //     printf("core id %d, weight %" PRId64 ", level %d: ", activeCores[i], core.weight, core.level);
    //     for (int j = 0; j < core.coreLits.size();j++)
    //         printf("%d(%d),", toInt(core.coreLits[j].lit), toInt(value(core.coreLits[j].lit)));
    //     printf("\n");
    // }
    // printf("\n");

    return true;
}*/

bool Solver::todoSecondLookahead()
{
    if (activeCores.size() == 0)
    {
        LOOKAHEAD_MULTILOCKS_SKIP++;
        return false;
    }

    bool res = false;
    int falseLitIndex = falseLitsRecord;
    CRef confl = CRef_Undef;
    while (falseLitIndex < falseLits.size() && !res)
    {
        Lit p = falseLits[falseLitIndex++];
        assert(value(p) == l_False);
        Var v = var(p);
        for (int i = 0; i < coresOfVar[v].size() && !res; i++)
        {
            LocalCore &core = localCores[coresOfVar[v][i]];
            core.falsifiedWeight = 0;
            for (int j = 0; j < core.coreLits.size(); j++)
            {
                if (value(core.coreLits[j].lit) == l_Undef)
                    uncheckedEnqueueForLK(core.coreLits[j].lit);
                else if (value(core.coreLits[j].lit) == l_False)
                    core.falsifiedWeight += core.coreLits[j].weight;
            }
            if (core.falsifiedWeight > core.weight)
                res = true;
            core.falsifiedWeight = 0;
        }
        if (!res)
        {
            confl = propagateForLK(true);
            if (confl != CRef_Undef || falseVar != var_Undef)
                res = true;
        }
    }

    if (!res)
    {
        LOOKAHEAD_MULTILOCKS_SKIP++;
        return false;
    }

    // printf("\n ***** Lookahead Multilocks %" PRIu64 " Start ***** \n", LOOKAHEAD_MULTILOCKS + 1);
    // printf("c UB=%" PRId64 ", laConflictCost=%" PRId64 ", countedWeight=%" PRId64 ", rest=%" PRId64 "\n",
    //     UB, laConflictCost, countedWeight, UB - laConflictCost - countedWeight);
    // for (int i = 0;i < activeCores.size();i++)
    // {
    //     LocalCore& core = localCores[activeCores[i]];
    //     printf("core id %d, weight %" PRId64 ", level %d: ", activeCores[i], core.weight, core.level);
    //     for (int j = 0; j < core.coreLits.size();j++)
    //         printf("%d(%d),", toInt(core.coreLits[j].lit), toInt(value(core.coreLits[j].lit)));
    //     printf("\n");
    // }
    // printf("\n");

    return true;
}

void Solver::lookaheadMultilocks()
{
    vec<Lit> out_learnt;
    setTrailRecord();
    UBconflictFlag = false;
    softConflictFlag = false;
    falseVar = var_Undef;
    falseCore = core_Undef;
    bool maxResDone = false;
    assert(unlockedVars.size() == 0);

    lastAssumed.clear();
    vec<Lit> allAssumed;
    allAssumed.clear();

    double startTime = cpuTime();

    while (countedWeight + laConflictCost < UB)
    {
        if (!enqueueAssumptionsMultilocks(allAssumed))
        {
            cancelUntilTrailRecordFillHeap();
            recoverCoreAfterLookahead(-1);
            // LAM_PRINT(LOOKAHEAD, "c nothing new.\n");
            break;
        }

        CRef confl = propagateForLKMultilocks();
        if (confl != CRef_Undef || falseVar != var_Undef || falseCore != core_Undef)
        {
            assert(falseVar == var_Undef || reason(falseVar) != CRef_Undef || falseCore != core_Undef);

            // if (confl != CRef_Undef)
            //     LAM_PRINT(LOOKAHEAD, "\nc find hard conflict %u \n", confl);
            // else if (falseVar != var_Undef)
            //     LAM_PRINT(LOOKAHEAD, "\nc find falseVar %d \n", falseVar);
            // else
            //     LAM_PRINT(LOOKAHEAD, "\nc find falseCore %d \n", falseCore);

            int coreid = pickCoreIdx();
            lookbackResetTrailMultilocks(confl, out_learnt, maxResDone, UB - countedWeight - laConflictCost);
            if (newcoreLits.size() > 0)
            {
                setCoreMultilock(coreid);
                counter++;
                for (int i = 0; i < lastAssumed.size(); i++)
                {
                    if (weights[var(lastAssumed[i])] == 0)
                        lastAssumed.clear();
                    else
                        seen2[var(lastAssumed[i])] = counter;
                }
                if (lastAssumed.size() > 0)
                {
                    lastAssumed.clear();
                    for (int i = allAssumed.size() - 1; i >= 0; i--)
                        if (seen2[var(allAssumed[i])] == counter)
                            lastAssumed.push(allAssumed[i]);
                }
                allAssumed.clear();
                cancelUntilTrailRecordUnsee();
                falseVar = var_Undef;
                falseCore = core_Undef;
            }
            else
            {
                cancelUntilTrailRecordUnsee();
                falseVar = var_Undef;
                falseCore = core_Undef;
                freeCores.push(coreid);
                resetConflicts_();
                allAssumed.clear();
                lastAssumed.clear();
                int prevLevel = decisionLevel();
                fixByLookahead(out_learnt);
                CRef confl = lPropagate();
                if (confl != CRef_Undef || softConflictFlag)
                {
                    if (confl != CRef_Undef)
                    {
                        LHconfl = confl;
                        softConflictFlag = false;
                        UBconflictFlag = false;
                    }
                    double endTime = cpuTime();
                    SECOND_LOOKAHEAD_TIME += (endTime - startTime);
                    return;
                }
                setTrailRecord();
                assert(UB > countedWeight);
                assert(laConflictCost == 0);
                assert(activeCores.size() == 0);
                lastConflLits.clear();
                maxResDone = false;
                double endTime = cpuTime();
                SECOND_LOOKAHEAD_TIME += (endTime - startTime);
                if (prevLevel == decisionLevel())
                    redoLookahead = true;
                return;
            }
        }
    }

    double endTime = cpuTime();
    SECOND_LOOKAHEAD_TIME += (endTime - startTime);

    if (countedWeight + laConflictCost >= UB)
    {
        LOOKAHEAD_MULTILOCKS_SUCCS++;
        assert(LHconfl == CRef_Undef);
        softConflictFlag = true;
        UBconflictFlag = true;
    }
}

// #define printTestedVar

// The involvedClauses stack stores the hard clauses that make disjoint conflicting soft clauses.
// If Ub is reached, the stack (together with the involved flag of each involved clauses) is cleared
// when analyzing the soft conflict
// Otherwise, it is cleared here before returning true.
bool Solver::lookahead()
{
    static int64_t thres = 2;
    static uint64_t prevConflicts = 0;
    static int64_t maxSuccLB = 0;
    static int64_t prevUB = 0;
    static int nbSample = 0;
    static double sumLB = 0;
    static double sumSQLB = 0;
    static double coef = 2;
    static int myLH = 0;
    static int mySucc = 0;
    static bool lastSucc = false;

    assert(UB > countedWeight);

    LHconfl = CRef_Undef;

#ifdef FLAG_NO_LA
    return false;
#endif

    int64_t lb = UB - countedWeight;
    if (lb > totalCost - satisfiedWeight - countedWeight) // Impossible to reach UB
        return false;

    if (UB != prevUB)
    {
        prevUB = UB;
        nbSample = 0;
        sumLB = 0;
        sumSQLB = 0;
    }

#ifndef FLAG_ALWAYS_LA
    int sampled = 0;
    if (conflicts > prevConflicts)
    {
        if (drand(random_seed) < 0.01)
        {
            thres = lb;
            sampled = 1;
        }
        else
            thres = maxSuccLB;
        prevConflicts = conflicts;
    }
    if (LOOKAHEAD == nbLKsuccess || lastSucc)
        thres = UB;

    if (lb > thres)
        return false;

    if (stepSizeLB > 0.06)
        stepSizeLB -= 0.000001;

    if (!sampled)
        myLH += 2;
#endif

    LOOKAHEAD++;

    assert(laConflictCost == 0);
    assert(activeCores.size() == 0);

    lastConflLits.clear();

#ifndef NDEBUG
    assert(lastCores.size() + freeCores.size() == localCores.size());

    /*for(int i = 0; i < freeCores.size(); i++) {
        assert(freeCores[i]<localCores.size());
        seen[freeCores[i]] = 1;
    }
    for(int i = 0; i < lastCores.size(); i++) {
        assert(lastCores[i] < localCores.size());
        seen[lastCores[i]] = 1;
    }
    for(int i=0; i < localCores.size(); i++){
        assert(seen[i]);
        seen[i]=0;
    }*/
#endif

    moreLookahead();

#ifndef FLAG_ALWAYS_LA
    if (softConflictFlag)
    {
        lastSucc = true;
        if (sampled)
        {
            assert(lb + countedWeight + laConflictCost >= UB);
            int64_t totalCost = countedWeight + laConflictCost + lb - UB;
            nbSample++;
            sumLB += totalCost;
            sumSQLB += totalCost * totalCost;
            double meanLB = ((double)sumLB) / nbSample;
            double meanSQLB = ((double)sumSQLB) / nbSample;
            double stddev = sqrt(meanSQLB - meanLB * meanLB);
            if (myLH > 0)
            {
                int rate = (mySucc * 100) / myLH;
                if (rate > 85 && (meanLB + coef * stddev) < UB)
                    coef += 0.1;
                else if (rate <= 70 && (meanLB + coef * stddev) > 1)
                    coef -= 0.1;
                // if ((meanLB + coef*stddev) > UB+1)
                //   coef = (UB+1 - meanLB)/stddev;
                //  printf("rate : %d, coef: %2.1lf, UB: "PRIu64", new thres: %d, mean: %4.2lf, stddev: %4.2lf\n", rate, coef, UB, (int)(meanLB + coef*stddev), meanLB, stddev);
            }
            else
            {
                if (coef < 2)
                    coef = 2;
                //	  printf("no LH\n");
            }
            maxSuccLB = (int64_t)(meanLB + coef * stddev);
            // myLH=0; mySucc = 0;
        }
        else
        {
            mySucc += 2;
        }

        nbLKsuccess++;
        totalPrunedLB += lb;
        totalPrunedLB2 += lb * lb;
    }
    else
    {
        lastSucc = false;
        if (!sampled)
        {
            mySucc += 1;
            /* if(LHconfl==CRef_Undef)
                mySucc += 1;
            else myLH-=2;*/
        }
        thres = lb - 1; //(lb+nbConfl)/2;
        prevConflicts = conflicts;
    }
#endif

    return activeCores.size() > 0 || LHconfl != CRef_Undef;
}

void Solver::printAroundSecondLookahead(bool before)
{
    if (before)
        LAM_PRINT(LOOKAHEAD, "\n ***** Lookahead %" PRIu64 " ***** \n", LOOKAHEAD);
    else
        LAM_PRINT(LOOKAHEAD, "\n ***** Lookahead Multilocks %" PRIu64 " End ***** \n", LOOKAHEAD_MULTILOCKS);

    LAM_PRINT(LOOKAHEAD, "c UB=%" PRId64 ", laConflictCost=%" PRId64 ", countedWeight=%" PRId64 ", rest=%" PRId64 "\n",
              UB, laConflictCost, countedWeight, UB - laConflictCost - countedWeight);
    for (int i = 0; i < activeCores.size(); i++)
    {
        LocalCore &core = localCores[activeCores[i]];
        LAM_PRINT(LOOKAHEAD, "core id %d, weight %" PRId64 ", level %d: ", activeCores[i], core.weight, core.level);
        for (int j = 0; j < core.coreLits.size(); j++)
        {
            assert(value(core.coreLits[j].lit) == l_Undef);
            LAM_PRINT(LOOKAHEAD, "%d(%" PRId64 "),", toInt(core.coreLits[j].lit), core.coreLits[j].weight);
        }
        LAM_PRINT(LOOKAHEAD, "\n");
    }
    LAM_PRINT(LOOKAHEAD, "\n");
}

void Solver::todoLookahead()
{
    bool first = true;
    while (true)
    {
        moreLookahead();
        if (TodoSecondLookahead)
        {
            printAroundSecondLookahead(true);
            if (first)
            {
                LOOKAHEAD_MULTILOCKS++;
                first = false;
            }
            redoLookahead = false;
            lookaheadMultilocks();
            if (redoLookahead)
            {
                REDO_LOOKAHEAD++;
                assert(activeCores.size() == 0);
                continue;
            }
            else
            {
                printAroundSecondLookahead(false);
                break;
            }
        }
        else
        {
            printAroundSecondLookahead(false);
            break;
        }
    }
}

bool Solver::lookaheadQscore()
{
    static int64_t thres = 2;
    static uint64_t prevConflicts = 0;
    static int64_t prevUB = 0;
    static double coef = 1;
    static int myLH = 0;
    static int mySucc = 0;

    assert(UB > countedWeight);
    LHconfl = CRef_Undef;
#ifdef FLAG_NO_LA
    return false;
#endif
    int64_t lb = UB - countedWeight;
    if (lb > totalCost - satisfiedWeight - countedWeight) // Impossible to reach UB
        return false;

    if (UB != prevUB)
    {
        if (UB > prevUB)
            for (int i = 0; i < Qscores.size(); i++)
                Qscores[i].no /= 2;
        prevUB = UB;
    }

#ifndef FLAG_ALWAYS_LA
    bool toDo;
    int nbFalsifiedSoftlit = falseLits.size();
    Qscore &qscore = Qscores[nbFalsifiedSoftlit];

    if (conflicts > prevConflicts)
    {
        if (drand(random_seed) < stepSizeLB / 2)
        {
            toDo = true;
        }
        else
        {
            if (myLH > 20)
            {
                int rate = (mySucc * 100) / myLH;
                if (rate > 75)
                {
                    coef += 0.1;
                    //  printf("succRate %d, coef %5.2f\n", rate, coef);
                }
                else if (rate < 60 && coef > 0.5)
                {
                    coef -= 0.1;
                    //  printf("succRate %d, coef %5.2f\n", rate, coef);
                }
            }
            toDo = (drand(random_seed) < (1 - (qscore.no - coef * qscore.yes)));

            if (!toDo)
                skipLAbyprba++;
        }
        prevConflicts = conflicts;
    }
    else if (lb <= thres)
        toDo = true;
    else
        toDo = false;

    if (LOOKAHEAD == nbLKsuccess)
        toDo = true;
    if (!toDo)
    {
        skipLA++;
        return true;
    }

    if (stepSizeLB > 0.04)
        stepSizeLB -= 0.00001;
    myLH += 1;
#endif

    LOOKAHEAD++;
    assert(laConflictCost == 0);
    assert(activeCores.size() == 0);
    lastConflLits.clear();
#ifndef NDEBUG
    assert(lastCores.size() + freeCores.size() == localCores.size());
#endif
    todoLookahead();

#ifndef FLAG_ALWAYS_LA
    if (softConflictFlag)
    {
        qscore.yes += stepSizeLB * (1 - qscore.yes);
        qscore.no *= (1 - stepSizeLB);
        mySucc += 1;
        totalPrunedLB += lb;
        totalPrunedLB2 += lb * lb;
    }
    else
    {
        qscore.no += stepSizeLB * (1 - qscore.no);
        qscore.yes *= (1 - stepSizeLB);
    }

    int rate = (mySucc * 100) / myLH;
    if (rate > 75)
        thres = lb;
    else if (rate > 50)
        thres = lb - 1;
    else
        thres = (lb + laConflictCost) / 2;
    prevConflicts = conflicts;
#endif
    return activeCores.size() > 0 || LHconfl != CRef_Undef;
}
