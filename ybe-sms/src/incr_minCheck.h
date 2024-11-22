//solver
//assumptions
//addassump
//removeassump?
//mincheck (solve, if sat extract perm, if unsat -> minimal)
//constructCNF

#include "useful.h"
#include "global.h"
#include "clause.h"
#include "solveGeneral.hpp"
#include "solveCadicalClass.hpp"

class MinCheckCNF;

class IncrMinCheck
{
public:
    IncrMinCheck();
    IncrMinCheck(cyclePerm_t &diag, shared_ptr<pperm_common> initialPart, bool isId);
    bool solvePartial(cycle_set_t &assump);
    bool solveComplete(cycle_set_t &assump);
    vector<int> extractPartialPerm();
    vector<int> extractCompletePerm();
    friend class MinCheckCNF;

private:
    cyclePerm_t diag;
    shared_ptr<pperm_common> initialPart;
    bool isId;

    void findWitness(cnf_t *cnf, int &nextFree);
    void findPartialWitness(cnf_t *cnf, int &nextFree);
    void findPartialWitnessV2(cnf_t *cnf, int &nextFree);
    void findPartialWitnessV3(cnf_t *cnf, int &nextFree);


    vector<vector<vector<lit_t>>> cycset_lits=vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));;
    vector<vector<vector<lit_t>>> perm_cycset_lits=vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));;
    vector<vector<lit_t>> perm_lits=vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0));
    vector<vector<vector<lit_t>>> largerEQ_lits=vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));;
    vector<vector<vector<lit_t>>> smallerEQ_lits=vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));;

    CaDiCaL::Solver *partialSolver;
    cnf_t part_cnf;
    int part_nextFreeVariable = 1;

    CaDiCaL::Solver *completeSolver;
    cnf_t comp_cnf;
    int comp_nextFreeVariable = 1;

    CaDiCaL::Solver *comp_Solver;
};
