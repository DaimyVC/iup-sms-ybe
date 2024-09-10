#include "incr_minCheck.h"
#include "solveCadicalClass.hpp"
#include "global.h"
#include "clause.h"
#include<queue>
#include<iterator>

IncrMinCheck::IncrMinCheck(){
    solver=new CaDiCaL::Solver();
    if (!solver->configure("sat"))
        EXIT_UNWANTED_STATE

    lit2entry.push_back(vector<int>{-1,-1,-1});
    highestOgCycsetVar = 0;
    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++)
            {
                if((i==j)||(i==k))
                    continue;
                lit2entry.push_back(vector<int>{i,j,k});
                highestOgCycsetVar++;
            }

    highestPermCycsetVar = highestOgCycsetVar;
    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++)
            {
                if((i==j)||(i==k))
                    continue;
                lit2entry.push_back(vector<int>{i,j,k});
                highestPermCycsetVar++;
            }

    highestPermVar = highestPermCycsetVar;
    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++){
            lit2entry.push_back(vector<int>{i,j});
            highestPermVar++;
        }
            
    findWitness(&cnf,nextFreeVariable,cycset_lits,perm_cycset_lits,perm_lits);
    
    for (auto clause : cnf)
    {
        if (clause.size() == 0)
            EXIT_UNWANTED_STATE

        for (auto lit : clause)
        {
            if (lit == 0)
                EXIT_UNWANTED_STATE
            solver->add(lit);
        }
        solver->add(0);
    }
    }

    bool IncrMinCheck::solve(cycle_set_t &assump){
        vector<lit_t> assumptions=vector<lit_t>{};
        for(int row = 0; row<problem_size; row++){
            for(int col=0; col<problem_size;col++){
                if(row==col)
                    continue;
                solver->assume(cycset_lits[row][col][assump.matrix[row][col]]);
            }
        }
        int res=solver->solve();
        return res==10;
    }

    bool IncrMinCheck::solve(){
        solver->assume(cycset_lits[0][1][2]);
        int res=solver->solve();
        return res==10;
    }

    vector<int> IncrMinCheck::extractPerm(){
        vector<int> perm = vector<int>(problem_size,-1);
        if(solver->state()==32){
            for(int i = 0; i<problem_size; i++){
                for(int j=0; j<problem_size; j++){
                    if(solver->val(perm_lits[i][j])>0){
                        perm[i]=j;
                        break;
                    }
                }
            }
        }
        return perm;
    }