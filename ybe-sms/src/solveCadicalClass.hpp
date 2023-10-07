#ifndef CADICAL_SOLVER_INTERFACE_H
#define CADICAL_SOLVER_INTERFACE_H

#include "global.h"
#include "solveGeneral.hpp"
#include "cadical.hpp"
#include <bits/stdc++.h>
#include <algorithm>

class CadicalSolver : public CommonInterface, public CaDiCaL::ExternalPropagator
{
private:
    CaDiCaL::Solver *solver;
    const std::vector<int> *model;
    bool redundant;

    bool changeInTrail = true; // checks whether the trail has changed since the last propagation step

    int highestEdgeVariable;
    vector<tuple<int, int, int>> lit2entry; // get for positive literal the corresponding edge

    vector<vector<int>> clauses;
    int highestVariable;
    int checkMode = false; // if true solver has finished and clauses are added by the normal "incremental interface"
    cycle_set_t currentCycleSet;
    vector<vector<vector<bool>>> fixedCycleSet; // true if entry in currentMatrix is fixed.
    deque<vector<int>> current_trail; // for each decision lvl store the assigned literals (only positive version)

    vector<vector<int>> literal2clausePos; // for each edge variable store clause which was used the last time.
    vector<vector<int>> literal2clauseNeg; // for each negation of an edge variable
public:
    CadicalSolver(cnf_t &cnf, int highestVariable);
    ~CadicalSolver() { solver->disconnect_external_propagator(); }

protected: // virtual classes from common interface
    void solve(vector<int> assumptions);
    bool solve(vector<int> assumptions, int timeout);

    cycle_set_t getCycleSet()
    {
        if (!checkMode)
        {
            return currentCycleSet;
        }
        else
        {
            cycle_set_t cycset;
            cycset.assignments=vector<vector<vector<truth_vals>>>(problem_size, vector<vector<truth_vals>>(problem_size, vector<truth_vals>(problem_size, Unknown_t)));
            cycset.matrix=vector<vector<int>>(problem_size, vector<int>(problem_size, -1));
            for (int i = 0; i < problem_size; i++)
                for (int j = 0; j < problem_size; j++)
                    for (int k = 0; k < problem_size; k++)
                    {
                        if (solver->val(cycset_lits[i][j][k])>0)
                        {
                            cycset.matrix[i][j]=k;
                            cycset.assignments[i][j][k]=True_t;
                        } 
                        if (solver->val(cycset_lits[i][j][k])<0)
                        {
                            cycset.assignments[i][j][k]=False_t;
                        } 
                    } 
            return cycset;
        }
    }

    void addClause(const vector<lit_t> &clause, bool redundant)
    {
        if (!checkMode)
            this->clauses.push_back(clause);
        else
        {
            // use incremental interface
            for (auto l : clause)
                solver->add(l);
            solver->add(0);
        }
    }

public:
    void notify_assignment(int lit, bool is_fixed)
    {
        changeInTrail = true;
        int absLit = abs(lit);
        if (!is_fixed) // push back literal to undo if current decission literal is changed
            current_trail.back().push_back(absLit);
        auto edge = lit2entry[absLit];
        if (lit > 0)
        {
            currentCycleSet.assignments[get<0>(edge)][get<1>(edge)][get<2>(edge)] = True_t;
            currentCycleSet.matrix[get<0>(edge)][get<1>(edge)] = get<2>(edge);
        }
        else
        {
            currentCycleSet.assignments[get<0>(edge)][get<1>(edge)][get<2>(edge)] = False_t;
        }
        if (is_fixed)
            fixedCycleSet[get<0>(edge)][get<1>(edge)][get<2>(edge)] = true;
    }

    void notify_new_decision_level()
    {
        current_trail.push_back(vector<int>());
    }

    void notify_backtrack(size_t new_level)
    {
        while (current_trail.size() > new_level + 1)
        {
            auto last = current_trail.back();
            for (int l : last)
            {
                tuple<int, int, int> entry = lit2entry[l];
                if (fixedCycleSet[get<0>(entry)][get<1>(entry)][get<2>(entry)])
                    continue;
                currentCycleSet.assignments[get<0>(entry)][get<1>(entry)][get<2>(entry)] = Unknown_t;
                if (currentCycleSet.matrix[get<0>(entry)][get<1>(entry)]==get<2>(entry))
                    currentCycleSet.matrix[get<0>(entry)][get<1>(entry)]=-1;
            }
            current_trail.pop_back();
        }
    }

    // currently not checked in propagator but with the normal incremental interface to allow adding other literals or even new once.
    bool cb_check_found_model(const std::vector<int> &model)
    {
        if (!clauses.empty())
            return false; // EXIT_UNWANTED_STATE only do check if there isn't another clause to add before
        // this->current_trail = &model;
        if (checkSolutionInProp)
        {
            return check();
        }
        return true;
    }

    bool check_solution()
    {
        if (!checkSolutionInProp)
        {
            checkMode = true;
            bool res = check();
            checkMode = false;
            return res;
        }
        return true;
    }

    bool cb_has_external_clause()
    {
        // PRINT_CURRENT_LINE
        // if no clause, then check whether a clause could be added. If already a clause present then just return clause.
        // if propagation is done in other function then not compute clauses here
        if (clauses.empty() && changeInTrail && !propagateLiteralsCadical)
        {
            changeInTrail = false;
            propagate();
        }

        // printf("Check for external clause: %ld\n", sym_breaking_clause.size());
        return !clauses.empty();
    }

    int cb_add_external_clause_lit()
    {
        // PRINT_CURRENT_LINE
        // printf("Call: Add external clause\n");
        vector<int> &lastClause = clauses[clauses.size() - 1];
        if (lastClause.empty())
        {
            clauses.pop_back(); // delete last clause
            // printf(" end clause\n");
            return 0;
        }
        else
        {
            // printf("Add external clause\n");
            int lit = lastClause.back();
            lastClause.pop_back();
            // printf("%d ", lit);
            return lit;
        }
    }

    // functions need to be defined
    int cb_decide() { return 0; }

    int cb_propagate()
    {
        // PRINT_CURRENT_LINE
        if (!propagateLiteralsCadical)
            return 0;

        // PRINT_CURRENT_LINE
        
        if (!changeInTrail)
            return 0;

        // PRINT_CURRENT_LINE

        // TODO changeInTrail = false;
        propagate();

        if (clauses.empty())
            return 0;

        auto lastClause = clauses.back();
        assert(!lastClause.empty());
        // find unassigned literal otherwise take last one; first check if clause is unit
        int nUnknown = 0;
        int unassigned = 0;
        for (auto l : lastClause)
        {
            auto entry = lit2entry[abs(l)];
            if (currentCycleSet.assignments[get<0>(entry)][get<1>(entry)][get<2>(entry)] == Unknown_t)
            {
                nUnknown++;
                unassigned = l;
            }
            else if (currentCycleSet.assignments[get<0>(entry)][get<1>(entry)][get<2>(entry)] == True_t && l > 0)
                return 0; // already satisfied
            else if (currentCycleSet.assignments[get<0>(entry)][get<1>(entry)][get<2>(entry)] == False_t && l < 0)
                return 0; // already satisfied
        }

        if (nUnknown == 1)
        {
            // notify_assignment(unassigned, false); // push back the clause to the current trail
            clauses.pop_back(); // delete last clause
            if (unassigned > 0)
                literal2clausePos[abs(unassigned)] = lastClause;
            else
                literal2clauseNeg[abs(unassigned)] = lastClause;
            // PRINT_CURRENT_LINE
            return unassigned;
        }
        return 0;
    }

    int cb_add_reason_clause_lit(int plit)
    {
        // PRINT_CURRENT_LINE
        if (plit > 0)
        {
            if (literal2clausePos[abs(plit)].empty())
                return 0;
            auto l = literal2clausePos[abs(plit)].back();
            literal2clausePos[abs(plit)].pop_back();
            return l;
        }
        else
        {
            if (literal2clauseNeg[abs(plit)].empty())
                return 0;
            auto l = literal2clauseNeg[abs(plit)].back();
            literal2clauseNeg[abs(plit)].pop_back();
            return l;
        }
    };
};

#endif
