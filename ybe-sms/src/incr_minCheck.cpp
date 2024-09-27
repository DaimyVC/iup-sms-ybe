#include "incr_minCheck.h"
#include "solveCadicalClass.hpp"
#include "global.h"
#include "clause.h"
#include<queue>
#include<iterator>

IncrMinCheck::IncrMinCheck(){};

IncrMinCheck::IncrMinCheck(cyclePerm_t &diag, shared_ptr<pperm_common> initialPart, bool isId){
    partialSolver=new CaDiCaL::Solver();
    if (!partialSolver->configure("unsat"))
        EXIT_UNWANTED_STATE
    
    this->diag=diag;
    this->isId=isId;
    this->initialPart=initialPart;

    part_lit2entry.push_back(vector<int>{-1,-1,-1});
    part_highestOgCycsetVar = 0;

    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++)
            {
                if((i==j)||(k==diag.diag[i]))
                    continue;
                part_lit2entry.push_back(vector<int>{i,j,k});
                part_highestOgCycsetVar++;
            }

    part_highestPermCycsetVar = part_highestOgCycsetVar;
    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++)
            {
                if((i==j)||(k==diag.diag[i]))
                    continue;
                part_lit2entry.push_back(vector<int>{i,j,k});

                comp_lit2entry.push_back(vector<int>{i,j,k});
            }

    part_highestPermVar = part_highestPermCycsetVar;

    for (int i = 0; i < problem_size; i++)
        for (int j : initialPart->options(i)){
            part_lit2entry.push_back(vector<int>{i,j});
            part_highestPermVar++;
        }

    findPartialWitness(&part_cnf,part_nextFreeVariable,part_cycset_lits,part_perm_cycset_lits,part_perm_lits,part_greater_lits,diag,initialPart,isId);

    for (auto clause : part_cnf)
    {
        if (clause.size() == 0)
            EXIT_UNWANTED_STATE

        for (auto lit : clause)
        {
            if (lit == 0)
                EXIT_UNWANTED_STATE
            partialSolver->add(lit);
        }
        partialSolver->add(0);
    }

    if(!allPart){
        completeSolver=new CaDiCaL::Solver();
        if (!completeSolver->configure("sat"))
            EXIT_UNWANTED_STATE

        comp_lit2entry.push_back(vector<int>{-1,-1,-1});
        comp_highestOgCycsetVar = 0;
        for (int i = 0; i < problem_size; i++)
            for (int j = 0; j < problem_size; j++)
                for (int k = 0; k < problem_size; k++)
                {
                    if((i==j)||(k==diag.diag[i]))
                        continue;
                    comp_lit2entry.push_back(vector<int>{i,j,k});
                    comp_highestOgCycsetVar++;
                }

        comp_highestPermCycsetVar = comp_highestOgCycsetVar;
        for (int i = 0; i < problem_size; i++)
            for (int j = 0; j < problem_size; j++)
                for (int k = 0; k < problem_size; k++)
                {
                    if((i==j)||(k==diag.diag[i]))
                        continue;
                    comp_lit2entry.push_back(vector<int>{i,j,k});
                    comp_highestPermCycsetVar++;
                }

        comp_highestPermVar = comp_highestPermCycsetVar;

        for (int i = 0; i < problem_size; i++)
            for (int j : initialPart->options(i)){
                comp_lit2entry.push_back(vector<int>{i,j});
                comp_highestPermVar++;
            }
                
        findWitness(&comp_cnf,comp_nextFreeVariable,comp_cycset_lits,comp_perm_cycset_lits,comp_perm_lits,diag,initialPart,isId);

        for (auto clause : comp_cnf)
        {
            if (clause.size() == 0)
                EXIT_UNWANTED_STATE

            for (auto lit : clause)
            {
                if (lit == 0)
                    EXIT_UNWANTED_STATE
                completeSolver->add(lit);
            }
            completeSolver->add(0);
        }

        comp_Solver=completeSolver;
        complete_cycset_lits=comp_cycset_lits;
        complete_perm_cycset_lits=comp_cycset_lits;
        complete_perm_lits=comp_perm_lits;
    } else {
        comp_Solver=partialSolver;
        complete_cycset_lits=part_cycset_lits;
        complete_perm_cycset_lits=part_cycset_lits;
        complete_perm_lits=part_perm_lits;
    }
    }

    bool IncrMinCheck::solvePartial(cycle_set_t &assump){
        vector<lit_t> assumptions=vector<lit_t>{};
        for(int row = 0; row<problem_size; row++){
            for(int col=0; col<problem_size;col++){
                if(row==col)
                    continue;
                int min = assump.bitdomains[row][col].firstel;
                for(int val=0; val<problem_size;val++){
                    if(val!=diag.diag[row]){
                        if(!assump.bitdomains[row][col].dom[val])
                            partialSolver->assume(-part_cycset_lits[row][col][val]);
                        else
                            partialSolver->assume(part_cycset_lits[row][col][val]);
                    }
                    if(val<min){
                        partialSolver->assume(part_greater_lits[row][col][val]);
                    } else {
                        partialSolver->assume(-part_greater_lits[row][col][val]);
                    }
                }
            }
        }
        partialSolver->limit("conflicts",limCon);
        partialSolver->limit("decisions",limDec);
        int res=partialSolver->solve();
        return res==10;
    }

    bool IncrMinCheck::solveComplete(cycle_set_t &assump){
        vector<lit_t> assumptions=vector<lit_t>{};
        for(int row = 0; row<problem_size; row++){
            for(int col=0; col<problem_size;col++){
                if(row==col)
                    continue;
                for(int val=0; val<problem_size;val++){
                    if(val!=diag.diag[row]){
                        if(val==assump.matrix[row][col])
                            comp_Solver->assume(complete_cycset_lits[row][col][val]);
                        else
                            comp_Solver->assume(-complete_cycset_lits[row][col][val]);
                        if(allPart){
                            if(val<assump.matrix[row][col]){
                                partialSolver->assume(part_greater_lits[row][col][val]);
                            } else {
                                partialSolver->assume(-part_greater_lits[row][col][val]);
                            }
                        }
                    }
                }
            }
        }
        int res=comp_Solver->solve();
        return res==10;
    }

    bool IncrMinCheck::solve(){
        partialSolver->assume(comp_cycset_lits[0][1][2]);
        int res=partialSolver->solve();
        return res==10;
    }

    vector<int> IncrMinCheck::extractPartialPerm(){
        vector<int> perm = vector<int>(problem_size,-1);
        if(partialSolver->state()==32){
            for(int i = 0; i<problem_size; i++){
                for(int j : initialPart->options(i)){
                    if(partialSolver->val(part_perm_lits[i][j])>0){
                        perm[i]=j;
                        break;
                    }
                }
            }
        }
        return perm;
    }

    vector<int> IncrMinCheck::extractCompletePerm(){
        vector<int> perm = vector<int>(problem_size,-1);
        if(comp_Solver->state()==32){
            for(int i = 0; i<problem_size; i++){
                for(int j : initialPart->options(i)){
                    if(comp_Solver->val(complete_perm_lits[i][j])>0){
                        perm[i]=j;
                        break;
                    }
                }
            }
        }
        return perm;
    }