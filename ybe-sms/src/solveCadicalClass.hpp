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

    int highestYBEVariable;
    int highestCNFVariable;
    vector<vector<int>> lit2entry; // get for positive literal the corresponding edge
    vector<vector<int>> clauses;
    int checkMode = false; // if true solver has finished and clauses are added by the normal "incremental interface"
    cycle_set_t currentCycleSet = cycle_set_t(problem_size,cycset_lits);
    vector<vector<vector<bool>>> fixedCycleSet; // true if entry in currentMatrix is fixed.
    deque<vector<int>> current_trail; // for each decision lvl store the assigned literals (only positive version)

    vector<vector<int>> literal2clausePos; // for each edge variable store clause which was used the last time.
    vector<vector<int>> literal2clauseNeg; // for each negation of an edge variable
    void fixDiag(const vector<int> &diag);
        
public:
    CadicalSolver(cnf_t &cnf, int highestVariable, vector<int> diag, const vector<vector<vector<lit_t>>>& cycset_lits, const vector<vector<vector<lit_t>>>& geq_lits, const statistics &stats);
    ~CadicalSolver() { solver->disconnect_external_propagator(); }

protected: // virtual classes from common interface
    void solve(vector<int> &assumptions);
    bool solve(vector<int> &assumptions, int timeout);

    cycle_set_t getCycleSet()
    {
        if (!checkMode)
        {
            return currentCycleSet;
        }
        else
        {
            cycle_set_t cycset(problem_size,currentCycleSet.cycset_lits);
            for (int i = 0; i < problem_size; i++)
                for (int j = 0; j < problem_size; j++)
                    for (int k = 0; k < problem_size; k++)
                    {
                        if(cycset_lits[i][j][k]!=0){
                            int v=solver->val(cycset_lits[i][j][k]);
                            if (v>0)
                            {
                                cycset.matrix[i][j]=k;
                                cycset.assignments[i][j][k]=True_t;
                                cycset.bitdomains[i][j].reset();
                                cycset.bitdomains[i][j].set(k);
                                for(int l=0; l<problem_size; l++){
                                    if(j!=l)
                                        cycset.bitdomains[i][l].reset(k);   
                                }
                            } 
                            if (v<0)
                            {
                                cycset.assignments[i][j][k]=False_t;
                                cycset.bitdomains[i][j].reset(k);
                            }
                        } else if (i==j){
                            cycset.matrix[i][j]=currentCycleSet.matrix[i][j];
                            cycset.assignments[i][j][k]=True_t;
                            cycset.bitdomains[i][j].reset();
                            cycset.bitdomains[i][j].set(k);
                            for(int l=0; l<problem_size; l++){
                                if(j!=l)
                                    cycset.bitdomains[i][l].reset(k);
                            }
                        }
                    }
            return cycset;
        }
    }

    bool is_decision(lit_t lit){
        return solver->is_decision(lit);
    }

    bool is_true(lit_t lit){
        return solver->val(lit);
    }

    void addClause(const vector<lit_t> &clause, bool redundant)
    {
        //printf("size clause: %d\n",clause.size());
        if (!checkMode)
            this->clauses.push_back(clause);
        else
        {
            // use incremental interface
            for (auto l : clause)
                solver->add(l);
            solver->add(0);
        }
        if(saveState && redundant){
            for(auto p : clause)
                fprintf(sbc,"%d ", p);
            fprintf(sbc,"0\n");
        } else if(saveState){
            for(auto p : clause)
                fprintf(sols,"%d ", p);
            fprintf(sols,"0\n");
        } else if(redundant){
            bool unitOrFalse=true;
            vector<int> unknown = vector<int>();
            for(auto l : clause){
                auto entry = lit2entry[abs(l)];
                auto asg = currentCycleSet.assignments[entry[0]][entry[1]][entry[2]];
                if(l>0){
                    if(asg==True_t){
                        unitOrFalse=false;
                        break;
                    } else if (asg==Unknown_t && find(unknown.begin(),unknown.end(),abs(l))==unknown.end()){
                        unknown.push_back(abs(l));
                    }
                }else if(l<0){
                    if(asg==False_t){
                        unitOrFalse=false;
                        break;
                    } else if (asg==Unknown_t && find(unknown.begin(),unknown.end(),abs(l))==unknown.end()){
                        unknown.push_back(abs(l));
                    }
                }
            }
            if(!unitOrFalse || unknown.size()>1){
                printf("GEEN UNIT/BACKTRACK CLAUSE!!\n");
            }
        }
        //solver->resources();
    }

    void prop(int r, int c, int val){
        for(int l=0; l<problem_size; l++){
            if(c==l)
                continue;
            else {
                if(currentCycleSet.bitdomains[r][l].numTrue!=1){
                    currentCycleSet.bitdomains[r][l].reset(val);
                    if(currentCycleSet.bitdomains[r][l].numTrue==1){
                        prop(r,l,currentCycleSet.bitdomains[r][l].firstel);
                    }
                }
            }
        }
    }

public:
    void notify_assignment(int lit, bool is_fixed)
    {
        changeInTrail = true;
        int absLit = abs(lit);
        if (!is_fixed) // push back literal to undo if current decission literal is changed
            {current_trail.back().push_back(absLit);}
        auto entry = lit2entry[absLit];
        if (lit > 0)
        {
            currentCycleSet.assignments[entry[0]][entry[1]][entry[2]] = True_t;
            currentCycleSet.matrix[entry[0]][entry[1]] = entry[2];
            currentCycleSet.bitdomains[entry[0]][entry[1]].reset();
            currentCycleSet.bitdomains[entry[0]][entry[1]].set(entry[2]);
            for(int l=0; l<problem_size; l++){
                if(entry[1]==l)
                    continue;
                else {
                    if(currentCycleSet.bitdomains[entry[0]][l].numTrue!=1)
                        currentCycleSet.bitdomains[entry[0]][l].reset(entry[2]);
                }
            }
        }
        else
        {
            currentCycleSet.assignments[entry[0]][entry[1]][entry[2]] = False_t;
            currentCycleSet.bitdomains[entry[0]][entry[1]].reset(entry[2]);
        }
        if (is_fixed)
            fixedCycleSet[entry[0]][entry[1]][entry[2]] = true;
    }

    void notify_new_decision_level()
    {
        current_trail.emplace_back();
    }

    void notify_backtrack(size_t new_level)
    {
        while (current_trail.size() > new_level + 1)
        {
            auto last = current_trail.back();
            for (int l : last)
            {
                auto entry = lit2entry[l];

                if (fixedCycleSet[entry[0]][entry[1]][entry[2]])
                    continue;

                if(currentCycleSet.assignments[entry[0]][entry[1]][entry[2]]==True_t){
                    currentCycleSet.matrix[entry[0]][entry[1]]=-1;
                    currentCycleSet.bitdomains[entry[0]][entry[1]].set();
                    for(int j=0;j<problem_size;j++){
                        if(j!=entry[1]){
                            if(currentCycleSet.matrix[entry[0]][j]!=-1){
                                currentCycleSet.bitdomains[entry[0]][entry[1]].reset(currentCycleSet.matrix[entry[0]][j]);
                            } else if (currentCycleSet.assignments[entry[0]][j][entry[2]]!=False_t){
                                currentCycleSet.bitdomains[entry[0]][j].set(entry[2]);
                            }
                        }

                        if(currentCycleSet.assignments[entry[0]][entry[1]][j]==False_t){
                            currentCycleSet.bitdomains[entry[0]][entry[1]].reset(j);
                        }
                    }
                }

                if(currentCycleSet.assignments[entry[0]][entry[1]][entry[2]]==False_t){
                    currentCycleSet.bitdomains[entry[0]][entry[1]].set(entry[2]);
                }

                currentCycleSet.assignments[entry[0]][entry[1]][entry[2]] = Unknown_t;
            }
            current_trail.pop_back();
        }
    }

    // currently not checked in propagator but with the normal incremental interface to allow adding other literals or even new once.
    bool cb_check_found_model(const std::vector<int> &/*model*/)
    {
        //printf("cb_check_found_model\n");
        if (!clauses.empty())
            return false; // EXIT_UNWANTED_STATE only do check if there isn't another clause to add before
        // this->current_trail = &model;
        return check();
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
    int cb_decide() {
        //cycle_set_t cyc = getCycleSet();
        for(int i=0; i<problem_size; i++){
            for(int j=0; j<problem_size; j++){
                if((i!=j) && currentCycleSet.bitdomains[i][j].numTrue>1){
                    int min = currentCycleSet.bitdomains[i][j].firstel;
                    return cycset_lits[i][j][min];
                }
            }
        }
        return 0;
    }

    int cb_propagate()
    {
        if(timelimit>0 && (duration_cast<seconds>(steady_clock::now()-stats.start).count())>timelimit){
            printf("TIME LIMIT!!!!!\n");
            solver->terminate();
            return 0;
        }
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
            if (currentCycleSet.assignments[entry[0]][entry[1]][entry[2]] == Unknown_t)
            {
                nUnknown++;
                unassigned = l;
            }
            else if (currentCycleSet.assignments[entry[0]][entry[1]][entry[2]] == True_t && l > 0)
                return 0; // already satisfied
            else if (currentCycleSet.assignments[entry[0]][entry[1]][entry[2]] == False_t && l < 0)
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
