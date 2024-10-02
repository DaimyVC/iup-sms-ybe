#include "useful.h"
#include "global.h"
#include "solveCadicalClass.hpp"
#include "cadical.hpp"
#include "minCheck_V2.h"

// add formula and register propagator
CadicalSolver::CadicalSolver(cnf_t &cnf, int highestVariable, vector<int> diag, vector<int> firstRow, vector<vector<vector<lit_t>>> lits, statistics stats)
{
    this->highestVariable = highestVariable;
    this->cycset_lits=lits;
    this->stats=stats;
    this->diag=diag;
    this->firstRow=firstRow;
    currentCycleSet = cycle_set_t(problem_size,lits);
    fixedCycleSet = vector<vector<vector<bool>>>(problem_size, vector<vector<bool>>(problem_size, vector<bool>(problem_size, false)));
    // The root-level of the trail is always there
    current_trail.push_back(std::vector<int>());

    if(!noEnum){
        string outputFilePath;
        outputFilePath.append(solOutput);
        outputFilePath.append("sols_");
        outputFilePath.append(to_string(problem_size));
        outputFilePath.append("_");
        for(auto d : diag)
            outputFilePath.append(to_string(d));
        outputFilePath.append(".txt");

        FILE *fp;
        fp = fopen(outputFilePath.c_str(),"w");
        this->output=fp;
    }

    
    /* string stateFilePath;
    string secFilePath;
    string sbcFilePath;
    if(readState || saveState){
        stateFilePath.append(solOutput);
        stateFilePath.append("state_");
        stateFilePath.append(to_string(problem_size));
        stateFilePath.append("_");
        for(auto d : diag)
            stateFilePath.append(to_string(d));
        stateFilePath.append(".txt");

        FILE *sfp;
        sfp = fopen(stateFilePath.c_str(),"a+");
        this->state=sfp;

        secFilePath.append(solOutput);
        secFilePath.append("sec_");
        secFilePath.append(to_string(problem_size));
        secFilePath.append("_");
        for(auto d : diag)
            secFilePath.append(to_string(d));
        secFilePath.append(".txt");

        FILE *secfp;
        secfp = fopen(secFilePath.c_str(),"a+");
        this->sols=secfp;

        sbcFilePath.append(solOutput);
        sbcFilePath.append("sbc_");
        sbcFilePath.append(to_string(problem_size));
        sbcFilePath.append("_");
        for(auto d : diag)
            sbcFilePath.append(to_string(d));
        sbcFilePath.append(".txt");

        FILE *sbcfp;
        sbcfp = fopen(sbcFilePath.c_str(),"a+");
        this->sbc=sbcfp;
    } */

    // only_propagating = false;
    solver = new CaDiCaL::Solver();
    
    //solver->configure("plain");
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
     
    highestEdgeVariable = 0;
    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++)
                if(!diagPart || (!smallerEncoding||(i!=j && k!=diag[i])))
                {
                    lit2entry.push_back(vector<int>{i,j,k});
                    highestEdgeVariable++;
                }

    // add clauses to solver
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

    

    //solver->write_dimacs("ybe.cnf");

    for (int i = 0; i < problem_size; i++)
        for (int j = 0; j < problem_size; j++)
            for (int k = 0; k < problem_size; k++)
                if(!diagPart || (i!=j&&(!smallerEncoding||k!=diag[i])))
                    solver->add_observed_var(cycset_lits[i][j][k]);

    literal2clausePos = vector<vector<int>>(highestEdgeVariable + 1);
    literal2clauseNeg = vector<vector<int>>(highestEdgeVariable + 1);

    if(diagPart)
        fixDiag(diag);

    if(fixedRow>0)
        fixFirstRow(firstRow);

    /* printCycleSet(currentCycleSet);
    printDomains(currentCycleSet); */

    /* if(readState){
        ifstream toParse(secFilePath);
        vector<vector<int>> toAdd;
        string temp;
        while (getline(toParse, temp)) {
            istringstream buffer(temp);
            vector<int> line((istream_iterator<int>(buffer)),istream_iterator<int>());
            toAdd.push_back(line);
        }

        ifstream toParse2(sbcFilePath);
        while (getline(toParse2, temp)) {
            istringstream buffer(temp);
            vector<int> line((istream_iterator<int>(buffer)),istream_iterator<int>());
            toAdd.push_back(line);
        }
        for(auto c : toAdd){
            for(int l : c){
                solver->add(l);
                printf("%d ",l);
            }
            printf("\n");
        }
    } */
        
    mincheck = new MinCheck_V2(diag,cycset_lits);

    //mincheck = MinimalityChecker(diag,cycset_lits);
}
void CadicalSolver::fixDiag(vector<int> diag)
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

void CadicalSolver::fixFirstRow(vector<int> firstRow)
{
    for(int k=0; k<problem_size; k++){
        if(diagPart && k==0)
            continue;
        currentCycleSet.bitdomains[0][k].set(firstRow[k]);
        fixedCycleSet[0][k][firstRow[k]]=true;
    }
    for(int k=0; k<problem_size; k++){
        if(diagPart && k==1)
            continue;
        currentCycleSet.bitdomains[1][k].set(firstRow[k]);
        fixedCycleSet[1][k][firstRow[k]]=true;
    }
}


void CadicalSolver::solve(vector<int> assumptions)
{
    do
    {
        for (auto lit : assumptions)
            solver->assume(lit);
        //solver->resources();
    } while (solver->solve() == 10);
    solver->statistics();
    
    if(!noEnum)
        fclose(output);
}

bool CadicalSolver::solve(vector<int>, int)
{
    printf("Not implemented yet\n");
    EXIT_UNWANTED_STATE
}
