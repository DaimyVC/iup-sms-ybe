#include "useful.h"
#include "global.h"
#include "solveCadicalClass.hpp"
#include "cadical.hpp"
#include "minCheck_V2.h"
#include "clause.h"

// add formula and register propagator
CadicalSolver::CadicalSolver(cnf_t &cnf, int highestCNFVariable, vector<int> diag, const vector<vector<vector<lit_t>>>& lits, const vector<vector<vector<lit_t>>>& g_lits, const statistics &stats)
{
    this->highestCNFVariable = highestCNFVariable;
    this->cycset_lits=lits;
    this->geq_lits=g_lits;
    this->stats=stats;
    this->diag=diag;
    currentCycleSet = cycle_set_t(problem_size,lits);
    fixedCycleSet = vector<vector<vector<bool>>>(problem_size, vector<vector<bool>>(problem_size, vector<bool>(problem_size, false)));
    // The root-level of the trail is always there
    current_trail.emplace_back();

    if(!noEnum){
        string outputFilePath;
        outputFilePath.append(solOutput);
        outputFilePath.append("sols_");
        outputFilePath.append(to_string(problem_size));
        outputFilePath.append("_");
        for(const auto d : diag)
            outputFilePath.append(to_string(d));
        outputFilePath.append(".txt");

        FILE *fp = fopen(outputFilePath.c_str(), "w");
        this->output=fp;
    }

    // only_propagating = false;
    solver = new CaDiCaL::Solver();
    
    if (!solver->configure("unsat"))
        EXIT_UNWANTED_STATE

    //solver->set("shuffle", 0);
    //solver->set("shufflequeue", 0);

    solver->set("lucky", 0);
    solver->set("walk", 0);
    solver->set("elim", 0);
    // solver->set("log", 1);
    // solver->set("debug", 1);

    // register propagator first
    solver->connect_external_propagator(this);

    lit2entry.push_back(vector<int>{-1,-1,-1}); // dummy pair for index 0
     
    highestYBEVariable = 0;
    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++)
                if((!smallerEncoding||(i!=j && k!=diag[i])))
                {
                    lit2entry.push_back(vector<int>{i,j,k});
                    highestYBEVariable++;
                }

    //define order over YBEvariables
    order_t order;

    //OLD ORDER
    for(int i=0; i<problem_size; i++){
        for(int j=0; j<problem_size; j++){
            if(i!=j){
                order.orderedCells.push_back(pair<int,int>(i,j));
                for(int k=problem_size-1;k>=0;k--){
                    int lit=cycset_lits[i][j][k];
                    if(lit!=0){}
                        order.orderedLits.push_back(lit);
                }
            }
        }
    }

    //Size-1 "compatible" order?
    // for(int i=0; i<problem_size; i++){
    //     for(int j=0; j<i; j++){
    //         order.orderedCells.push_back(pair<int,int>(i,j)); 
    //         order.orderedCells.push_back(pair<int,int>(j,i));
    //     }
    // }

    //Statically break a selection of symmetries (if identity diagonal)
    if(staticSBP){
        if(SBPPath!=""){
            FILE * SBPFile = fopen(SBPPath.c_str(),"r");
            char line[4096];
            while (fgets(line, sizeof(line), SBPFile)) {
                vector<int> perm;
                stringstream ss(line);
                string num;
                while (getline(ss, num, ',')) {
                    perm.push_back(stoi(num));
                }
                if(perm.size()==problem_size){
                    addStaticSBP(&cnf, this->highestCNFVariable, cycset_lits, geq_lits, diag, order, perm, limSBP,oldSBP);
                }
            }
            fclose(SBPFile);
        } else {
            auto breakPerm = vector<int>(problem_size);
            iota(breakPerm.begin(),breakPerm.end(),0);

            for(int i=0; i<problem_size; i++){
                swap(breakPerm[i],breakPerm[(i+1)%problem_size]);
                addStaticSBP(&cnf, this->highestCNFVariable, cycset_lits, geq_lits, diag, order, breakPerm, limSBP, oldSBP);
                swap(breakPerm[i],breakPerm[(i+1)%(problem_size)]);
            }
        }
    }

    // add clauses to solver
    for (const auto& clause : cnf)
    {
        if (clause.empty())
            EXIT_UNWANTED_STATE

        for (const auto lit : clause)
        {
            if (lit == 0)
                EXIT_UNWANTED_STATE
            solver->add(lit);
        }
        solver->add(0);
    }

    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++)
                if((i!=j&&(!smallerEncoding||k!=diag[i])))
                    solver->add_observed_var(cycset_lits[i][j][k]);

    literal2clausePos = vector<vector<int>>(highestYBEVariable + 1);
    literal2clauseNeg = vector<vector<int>>(highestYBEVariable + 1);

    fixDiag(diag);

    mincheck = new MinCheck_V2(diag,cycset_lits,order);

    
}
void CadicalSolver::fixDiag(const vector<int> &diag)
{
    for(int i=0; i<problem_size; i++){
        for(int k=0; k<problem_size; k++){
            if(k!=diag[i]){
                currentCycleSet.assignments[i][i][k]=False_t;
            } else {
                currentCycleSet.assignments[i][i][k]=True_t;
            }
            if(k!=i){
                currentCycleSet.bitdomains[i][k].reset(diag[i]);
            } else {
                currentCycleSet.bitdomains[i][k].reset();
                currentCycleSet.bitdomains[i][k].set(diag[i]);
            }
            fixedCycleSet[i][i][k]=true;
        }       
    currentCycleSet.matrix[i][i]=diag[i];
    }
}


void CadicalSolver::solve(vector<int> &assumptions)
{
    do
    {
        for (const auto lit : assumptions)
            solver->assume(lit);
        //solver->resources();
    } while (solver->solve() == 10);
    solver->statistics();
    
    if(!noEnum)
        fclose(output);

    mincheck->counter.exportCounts(15);
}

bool CadicalSolver::solve(vector<int> &, int)
{
    printf("Not implemented yet\n");
    EXIT_UNWANTED_STATE
}
