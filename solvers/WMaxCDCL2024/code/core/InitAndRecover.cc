#include "Solver.h"

void Solver::trimSoftLiterals(bool first)
{
    totalCost = 0;
    int i, j;
    allSoftLits.clear();
    for (i = 0, j = 0; i < unitSoftLits.size(); i++)
    {
        Lit p = unitSoftLits[i];
        Var v = var(p);
        if (!isSoftLits(v))
            continue;

        if (value(p) == l_Undef)
        {
            totalCost += weights[v];
            unitSoftLits[j++] = p;
            allSoftLits.push(p);
        }
        else
        {
            if (value(p) == l_False)
                fixedCost += weights[v];
            else
                satCost += weights[v];
            removeSoftLit(p);
        }
    }
    unitSoftLits.shrink(i - j);

    for (i = 0, j = 0; i < nonUnitSoftLits.size(); i++)
    {
        Lit p = nonUnitSoftLits[i];
        Var v = var(p);
        if (!isSoftLits(v))
            continue;

        if (value(p) == l_Undef)
        {
            totalCost += weights[v];
            nonUnitSoftLits[j++] = p;
            allSoftLits.push(p);
        }
        else
        {
            if (value(p) == l_False)
                fixedCost += weights[v];
            else
                satCost += weights[v];
            removeSoftLit(p);
        }
    }
    nonUnitSoftLits.shrink(i - j);
    nSoftLits = unitSoftLits.size() + nonUnitSoftLits.size();
    weights.copyTo(weightsBckp);

    if (first)
    {
        counter++;
        for (i = 0, j = 0; i < softLitsPBorder.size(); i++)
        {
            Lit p = softLitsPBorder[i];
            if (value(p) == l_Undef)
            {
                Lit q = imply[toInt(p)];
                if (isSoftLits(p) && seen2[var(p)] < counter)
                {
                    softLitsPBorder[j++] = p;
                    seen2[var(p)] = counter;
                }
                else if (!isSoftLits(p) && q != lit_Undef && seen2[var(q)] < counter && value(q) == l_Undef)
                {
                    softLitsPBorder[j++] = q;
                    seen2[var(q)] = counter;
                }
            }
        }
        softLitsPBorder.shrink(i - j);
        assert(softLitsPBorder.size() == nSoftLits);
    }
    else
    {
        for (i = 0, j = 0; i < softLitsPBorder.size(); i++)
        {
            Lit p = softLitsPBorder[i];
            Var v = var(p);
            if (!isSoftLits(v))
                continue;

            if (value(p) == l_Undef)
                softLitsPBorder[j++] = p;
        }
        softLitsPBorder.shrink(i - j);
        assert(softLitsPBorder.size() == nSoftLits);
    }

    objForSearch = totalCost;
    fixedCostBySearch = fixedCost;

    printf("c fixedCost %" PRId64 ", satCost %" PRId64 ", totalFixedVars %d, objForSearch: %" PRId64 "\n\n",
           fixedCost, satCost, trail.size(), objForSearch);

    // staticNbVars = nVars();
    falseLits.clear();
    countedWeight = 0;
    // At this point, all variables have been created and renamed.
    // Some data structures that had not been used before, especially the ones indexed by var, are now created
}

void Solver::trimSoftLiterals2()
{
    for (int i = 0; i < amos.size(); i++)
        for (int j = 0; j < amos[i].size(); j++)
            amosOfVar[var(amos[i][j])] = i;

    rebuildOrderHeap();

    hardenHeap.clear();
    minWeight = INT64_MAX;
    for (int i = 0; i < nSoftLits; i++)
    {
        Var v = var(allSoftLits[i]);
        assert(weights[v] > 0);
        if (weights[v] < minWeight)
            minWeight = weights[v];
        hardenHeap.insert(v);
    }
}

void Solver::saveClausesAndSoftLits()
{
    // save the original context before solving, of which the purpose is to restore this context
    // after proving an unfeasible UB
    int i, j;
    for (i = 0, j = 0; i < clauses.size(); i++)
    {
        CRef cr = clauses[i];
        if (!removed(cr))
        {
            Clause &c = ca[cr];
            if (!satisfied(c))
            {
                clauses[j++] = cr;
                for (int k = 0; k < c.size(); k++)
                    if (value(c[k]) == l_Undef)
                        savedClauseLits.push(c[k]);
                savedClauseLits.push(lit_Undef);
            }
            else
                removeClause(cr);
        }
    }
    clauses.shrink(i - j);

    for (i = 0; i < softLitsPBorder.size(); i++)
    {
        Lit p = softLitsPBorder[i];
        assert(p == softLits[var(p)]);
        savedSoftLitsPBorder.push(p);
    }
    for (i = 0; i < allSoftLits.size(); i++)
    {
        Lit p = allSoftLits[i];
        assert(p == softLits[var(p)]);
        savedAllSoftLits.push(p);
    }
    weights.copyTo(savedWeights);
    for (int v = 0; v < nVars(); v++)
        savedDecision[v] = decision[v];
}

bool Solver::doEliminationInInitialization()
{
    if (!eliminate())
        return false; // l_False;
    return true;
}

void Solver::initStatus()
{
    initTrail = trail.size();
    initNbEliminatedVars = eliminatedVars.size();
    initNbElimclauses = elimclauses.size();

    initNbEquivLits = equivLits.size();
    initFeasibleNbEq = feasibleNbEq;
    initPrevEquivLitsNb = prevEquivLitsNb;
    initNbSoftEq = nbSoftEq;
    initPrevNbSoftEq = prevNbSoftEq;

    //  initCountedWeight = countedWeight;
    // initSatisfiedWeight = satisfiedWeight;
}

bool Solver::doPreprocessingInInitialization()
{
    if (!simplifyOriginalClauses(clauses))
    {
#ifdef BIN_DRUP
        if (drup_file)
            binDRUP_flush(drup_file);
#endif
        return false;
    }
    allSoftLits.copyTo(softLitsPBorder);

    /*if (!findImplications()) {
        printf("c problem solved by preprocessing\n");
        return l_False;
    }*/
    if (!findConflictSoftLits())
    {
        printf("c problem solved by preprocessing\n");
        return false;
    }
    if (!findAMOs())
    {
        printf("c problem solved by preprocessing\n");
        return false;
    }
    /*
    if (!detectInitConflicts()) {
        printf("c problem solved by preprocessing2\n");
        return l_False;
    }*/
    return true;
}

void Solver::initLookaheadAndCores()
{
    LOOKAHEAD = 0, savedLOOKAHEAD = 0, nbLKsuccess = 0, savednbLKsuccess = 0;
    TodoSecondLookahead = false;
    SECOND_LOOKAHEAD_TIME = 0;
    LOOKAHEAD_MULTILOCKS = 0, LOOKAHEAD_MULTILOCKS_SUCCS = 0, LOOKAHEAD_MULTILOCKS_MULTICORES = 0, LOOKAHEAD_MULTILOCKS_SKIP = 0;
    laConflictCost = 0;
    falseVar = var_Undef;
    falseCore = -1;

    localCores.clear();
    activeCores.clear();
    freeCores.clear();
    lastCores.clear();

    assignedVars.clear();

    // multilocks
    // lockDecreasedCores.clear();
    // decreasedLocks.clear();
    unlockedVars.clear();
    subCores.clear();

    litsTobeAssigned.clear();
    coresTobeAssigned.clear();
}

bool Solver::initialization()
{
    addHardClausesForSoftClauses();
    initLookaheadAndCores();
    staticNbVars = nVars();

    add_tmp.clear();
    softConflictFlag = false;
    next_C_reduce = 0;
    UBconflictFlag = false;

    lk_propagations = 0;
    stepSizeLB = 0.4;
    subconflicts = 0;
    totalPrunedLB = 0;
    totalPrunedLB2 = 0;
    derivedCost = 0;
    nbHardens = 0;
    fixedByHardens = 0;
    nbSavedLits = 0;

    rootConflCost = 0;
    redoLookahead = false;
    REDO_LOOKAHEAD = 0;
    fixedCost = 0;
    feasible = false;

    countedWeight = 0;
    satisfiedWeight = 0;

    hardens.clear();

    UB = INT64_MAX;
    if (initUB < INT64_MAX)
    {
        if (solutionCost > initUB)
        {
            printf("c problem solved by preprocessing\n");
            return false;
        }
        else
            UB = initUB - solutionCost + 1;
    }
    infeasibleUB = 0;
    WithNewUB = false;

    if (!doPreprocessingInInitialization())
        return false;
    staticNbVars = nVars();
    trimSoftLiterals(true);
    trimSoftLiterals2();

    UB = totalCost + 1;
    // int savedTrail = trail.size();
    initTrail = trail.size();

    if (!doEliminationInInitialization())
        return false;

    // if (savedTrail < trail.size())
    //{
    trimSoftLiterals(false);
    derivedCost += derivedEmptyWeight;
    derivedEmptyWeight = 0;
    infeasibleUB = 0;
    //}
    trimSoftLiterals2();

    saveClausesAndSoftLits();
    initStatus();

    for (int i = 0; i < equivLits.size(); i++)
    {
        Lit p = equivLits[i];
        savedEquivLits.push(p);
        savedEquivLits.push(rpr[toInt(p)]);
    }

    Qscores.growTo(allSoftLits.size() + 1, Qscore(0, 0));
    return true;
}

void Solver::recoverClausesAndSoftLits()
{
    // reconstitute the original clauses
    for (Var v = 0; v < nVars(); v++)
    {
        assert(!decision[v] || !eliminated[v]);

        Lit p = mkLit(v);
        watches[p].clear();
        watches[~p].clear();
        watches_bin[p].clear();
        watches_bin[~p].clear();
        involved[v] = 0;
        seen[v] = 0;
        vardata[v].reason = CRef_Undef;
    }
    // involvedLits.clear();
    clauses.clear();
    ClauseAllocator to(ca.size() - ca.wasted());
    vec<Lit> lits;
    for (int i = 0; i < savedClauseLits.size(); i++)
    {
        Lit p = savedClauseLits[i];
        if (p == lit_Undef)
        {
            CRef cr = to.alloc(lits, false);
            clauses.push(cr);
            lits.clear();
        }
        else
        {
            lits.push(p);
            assert(value(p) == l_Undef);
        }
    }
    vec<Lit> dummy(1, lit_Undef);
    bwdsub_tmpunit = to.alloc(dummy);
    to.moveTo(ca);
    for (int i = 0; i < clauses.size(); i++)
        attachClause(clauses[i]);

    learnts_local.clear();
    learnts_tier2.clear();
    hardens.clear();
    hardens_lim.shrink(hardens_lim.size());
    PBC.clear();
    CCPBadded = false;
    learnts_core.clear();
    isetClauses.clear();

    dynVars.clear();
    for (int i = nVars() - 1; i >= staticNbVars; i--)
    {
        decision[i] = false;
        dynVars.push(i);
    }

    for (int i = 0; i < savedWeights.size(); i++)
    {
        weights[i] = savedWeights[i];
        weightsBckp[i] = savedWeights[i];
    }

    softLitsPBorder.clear();
    for (int i = 0; i < savedSoftLitsPBorder.size(); i++)
    {
        Lit p = savedSoftLitsPBorder[i];
        softLits[var(p)] = p;
        softLitsPBorder.push(p);
    }
    allSoftLits.clear();
    hardenHeap.clear();
    for (int i = 0; i < savedAllSoftLits.size(); i++)
    {
        Lit p = savedAllSoftLits[i];
        // assert(toInt(p) >= 0);
        softLits[var(p)] = p;
        allSoftLits.push(p);
        hardenHeap.insert(var(p));
    }
    UB += derivedEmptyWeight;
    infeasibleUB += derivedEmptyWeight;
    totalCost += derivedEmptyWeight;
    derivedEmptyWeight = 0;

    for (Var v = 0; v < staticNbVars; v++)
        decision[v] = savedDecision[v];

    rebuildOrderHeap();
}

void Solver::recoverEliminatedVariables()
{
    for (int i = initNbEliminatedVars; i < eliminatedVars.size(); i++)
        eliminated[eliminatedVars[i]] = false;
    eliminatedVars.shrink(eliminatedVars.size() - initNbEliminatedVars);
    elimclauses.shrink(elimclauses.size() - initNbElimclauses);
}

/*void Solver::clearHardens()
{
    for (int i = 0; i < hardens.size(); i++)
    {
        assert(ca[hardens[i]].mark() != 1);
        ca[hardens[i]].mark(1);
        ca.free(hardens[i]);
    }
    hardens.shrink_(hardens.size());
    hardens_lim.shrink(hardens_lim.size());
}*/

void Solver::recoverEquivlentLits()
{
    for (int i = equivLits.size() - 1; i >= 0; i--)
    {
        Lit p = equivLits[i];
        assert(rpr[toInt(~p)] == ~rpr[toInt(p)]);
        rpr[toInt(p)] = lit_Undef;
        rpr[toInt(~p)] = lit_Undef;
    }
    equivLits.shrink(equivLits.size());

    for (int i = 0; i < savedEquivLits.size(); i += 2)
    {
        Lit p = savedEquivLits[i];
        rpr[toInt(p)] = savedEquivLits[i + 1];
        rpr[toInt(~p)] = ~savedEquivLits[i + 1];
        equivLits.push(p);
    }
    assert(equivLits.size() == initNbEquivLits);

    feasibleNbEq = initFeasibleNbEq;
    prevEquivLitsNb = initPrevEquivLitsNb;
    nbSoftEq = initNbSoftEq;
    prevNbSoftEq = initPrevNbSoftEq;
}

void Solver::resetTrailRecordBeginning(int beginning)
{
    qhead = beginning;
    trail.shrink(trail.size() - beginning);
    trail_lim.shrink(trail_lim.size());
    falseLits.shrink(falseLits.size());
    falseLits_lim.shrink(falseLits_lim.size());
    countedWeight_lim.shrink(countedWeight_lim.size());
    countedWeight = 0;
    satisfiedWeight_lim.shrink(satisfiedWeight_lim.size());
    satisfiedWeight = 0;
}

void Solver::cancelUntilBeginning(int beginning)
{
    for (int c = trail.size() - 1; c >= beginning; c--)
    {
        Var x = var(trail[c]);
        if (!VSIDS)
        {
            uint32_t age = conflicts - picked[x];
            if (age > 0)
            {
                double adjusted_reward = ((double)(conflicted[x] + almost_conflicted[x])) / ((double)age);
                double old_activity = activity_CHB[x];
                activity_CHB[x] = step_size * adjusted_reward + ((1 - step_size) * old_activity);
                if (order_heap_CHB.inHeap(x))
                {
                    if (activity_CHB[x] > old_activity)
                        order_heap_CHB.decrease(x);
                    else
                        order_heap_CHB.increase(x);
                }
            }
#ifdef ANTI_EXPLORATION
            canceled[x] = conflicts;
#endif
        }
        assigns[x] = l_Undef;
        if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
            polarity[x] = sign(trail[c]);
        insertSoftLitOrder(x);
        insertVarOrder(x);
        seen[x] = 0;
        if (isSoftLits(x))
        {
            hardenHeap.update(x);
            hardened[x] = false;
        }
    }

    resetTrailRecordBeginning(beginning);
    recoverEliminatedVariables();
    for (Var v = 0; v < staticNbVars; v++)
        decision[v] = savedDecision[v];
    recoverEquivlentLits();
    recoverClausesAndSoftLits();
}
