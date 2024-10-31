#include "incr_minCheck.h"
#include "solveCadicalClass.hpp"
#include "global.h"
#include "clause.h"
#include<queue>
#include<iterator>

IncrMinCheck::IncrMinCheck(){};

IncrMinCheck::IncrMinCheck(cyclePerm_t &diag, shared_ptr<pperm_common> initialPart, bool isId){
    partialSolver=new CaDiCaL::Solver();
    if (!partialSolver->configure("sat"))
        EXIT_UNWANTED_STATE
    
    this->diag=diag;
    this->isId=isId;
    this->initialPart=initialPart;

    int nextFree = 1;

    //Encode cycle set lits
    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++){
            for (int k = 0; k < problem_size; k++){
                if((i==j) || (diag.diag[i]==k))
                    continue;
                cycset_lits[i][j][k] = nextFree++;
                perm_cycset_lits[i][j][k] = nextFree++;
            }
        }

    
    //Encode possible permutations
    if(isId){
        for(int i=0; i<problem_size;i++)
            for(int j=0;j<problem_size;j++)
                perm_lits[i][j]=nextFree++;
    } else {
        for(int i=0; i<problem_size;i++)
            for(int j : initialPart->options(i))
                perm_lits[i][j]=nextFree++;
    }
    
    comp_nextFreeVariable=nextFree;

    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++){
            for (int k = 0; k < problem_size; k++){
                if(i==j)
                    continue;
                largerEQ_lits[i][j][k] = nextFree++;
                smallerEQ_lits[i][j][k] = nextFree++;
            }
        }
    
    part_nextFreeVariable=nextFree;

    if(newIncr){
        findPartialWitnessV2(&part_cnf,part_nextFreeVariable);
    } else {
        findPartialWitness(&part_cnf,part_nextFreeVariable);
    }

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
        if (!completeSolver->configure("unsat"))
            EXIT_UNWANTED_STATE
        
        findWitness(&comp_cnf,comp_nextFreeVariable);

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

    } else {
        comp_Solver=partialSolver;
    }
    }

    bool IncrMinCheck::solvePartial(cycle_set_t &assump){
        for(int row = 0; row<problem_size; row++){
            for(int col=0; col<problem_size;col++){
                if(row==col)
                    continue;
                int min = assump.bitdomains[row][col].firstel;
                for(int val=0; val<problem_size;val++){
                    if(val!=diag.diag[row]){
                        if(!assump.bitdomains[row][col].dom[val]){
                            partialSolver->assume(-cycset_lits[row][col][val]);
                        }
                        else {
                            partialSolver->assume(cycset_lits[row][col][val]);
                        }
                    }
                    if(val==0)
                        continue;
                    if(val<=min){
                        partialSolver->assume(largerEQ_lits[row][col][val]);
                    } else {
                        partialSolver->assume(-largerEQ_lits[row][col][val]);
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
        for(int row = 0; row<problem_size; row++){
            for(int col=0; col<problem_size;col++){
                if(row==col)
                    continue;
                for(int val=0; val<problem_size;val++){
                    if(val!=diag.diag[row]){
                        if(val==assump.matrix[row][col]){
                            comp_Solver->assume(cycset_lits[row][col][val]);
                        } else {
                            comp_Solver->assume(-cycset_lits[row][col][val]);
                        }
                        if(allPart && val!=0){
                            if(val<=assump.matrix[row][col]){
                                comp_Solver->assume(largerEQ_lits[row][col][val]);
                            } else {
                                comp_Solver->assume(-largerEQ_lits[row][col][val]);
                            }
                        }
                    }
                }
            }
        }
        int res=comp_Solver->solve();
        return res==10;
    }

    vector<int> IncrMinCheck::extractPartialPerm(){
        vector<int> perm = vector<int>(problem_size,-1);
        if(partialSolver->state()==32){
            for(int i = 0; i<problem_size; i++){
                for(int j : initialPart->options(i)){
                    if(partialSolver->val(perm_lits[i][j])>0){
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
                    if(comp_Solver->val(perm_lits[i][j])>0){
                        perm[i]=j;
                        break;
                    }
                }
            }
        }
        return perm;
    }