#include "useful.h"
#include "global.h"
#include "clause.h"
#include "solveGeneral.hpp"
#include "solveCadicalClass.hpp"
#include <fstream>
#include <sstream>
#include <argp.h>

int nextFreeVariable;
int problem_size = 3;
int checkFreq = 40;
int timelimit = -1;
clock_t startOfSolving;
bool incrMincheck = false;
bool allPart = false;
bool indecomp = false;
bool propagateMincheck = false;
bool oldBreakingClauses = false;
bool propagateLiteralsCadical = false;
bool checkSolutionInProp = false;
int maxDepth = INT_MAX;
int maxMC = INT_MAX;
bool doFinalCheck=false;
bool smallerEncoding=false;
bool minCheckOld = false;
bool useBit = false;
bool useRange = false;
bool noCommander = false;
int logging = 0;
int limDec = -1;
int limCon = -1;
int limCls = -1;
int limSBP = -1;
bool oldSBP = false;
bool noEnum = false;
int rseed = 1771177;
bool staticSBP = false;

string solOutput="";
string logOutput="";
string SBPPath="";
bool saveState = false;
bool readState = false;

auto diagonal=vector<int>();

const char *argp_program_version="YBE-SMS 1.0";
const char *argp_program_bug_address ="<daimy.vancaudenberg@kuleuven.be>";
static char doc[] = "YBE-SMS - A tool for the enumeration of set-theoretic solutions to the Yang-Baxter equation.";
static struct argp_option options[] = {
    {"noEnum",  'n',    0,  0,  "Only count solutions, do not save them in a database.", 0},
    {"size",  's',    "SIZE",  0,  "Use the incremental approach.", 0   },
    {"diag",  200,  "DIAG",   OPTION_ARG_OPTIONAL, "Fixes the given array (f.e. --diag 0,1,2,3,) on the diagonal. If no diagonal is given, all diagonals are solved in parallel.", 0},
    {"indecomposable",  201,  0,  0,   "Only enumerate indecomposable solutions.", 0},

    {"noCommander",  300,  0,  0,   "Don't use the commander encoding for the exactly one constraints.", 0},
    {"smallerEncoding",  301,  0,  0,   "Use an encoding that is optimized by propagating the information obtained by fixing the diagonal.", 0},
    {"useBit",  302,  0,  OPTION_HIDDEN,   "", 0},
    {"oldBreak",  303,  0,  0,   "Do not use the breaking clauses that are optimized using the available domain knowledge.", 0},

    {"checkSols",  400,  0,  0,   "Check partial solutions for their minimality.", 0},
    {"propLits",  401,  0,  0,    "", 0},
    {"checkFreq",  402,  "FREQ",  0,   "If partial solutions are checked, define the frequency with which to check partial solutions.", 0},
    {"time",  403,  "TIMELIM",  0,    "Define a time limit for the main solver. !!ENUMERATION COULD BE INCOMPLETE!!", 0},
    {"out", 404, "FILE",  0,   "Write the enumerated solutions to the given file.", 0},
    {"log",  'l',  "FILE",  0,   "Write the log to the given file.", 0},
    {"logging",  405,  "VERBLEVEL",  OPTION_HIDDEN,   "FOR DEBUG ONLY", 0},

    {"allPart",  'p',    0,  0,  "Use only one incremental solver (with the partial encoding) for the minimality check. !!USE WITH INCREMENTAL APPROACH!!"   , 0},
    {"incr",  'i',    0,  0,  "Use the incremental approach.",0   },
    {"limDec",  500,    "DECLIM",  0,  "Limit the number of decisions made during partial incremental minimality checks. !!USED WITH INCREMENTAL APPROACH!!"   , 0},
    {"limCon",  501,    "CONLIM",  0,  "Limit the number of conflicts encountered during partial incremental minimality checks. !!USED WITH INCREMENTAL APPROACH!!"   , 0},
    {"limCls",  502,    "CLSLIM",  0,  "Limit the maximum length of clauses added during partial incremental minimality checks. !!USED WITH INCREMENTAL APPROACH!!"   , 0},
    {"limSBP",  506,    "LIMSBP",  0,  "Limit the maximum of aux vars introduced in statically added SBPs"   , 0},
    {"oldSBP",  507,    0,  0,  "Limit the maximum of aux vars introduced in statically added SBPs"   , 0},
    {"exportSBP",  503,    0,  0,  "Export the generated SBP files to an outputfile for use with readSBP !!USED WITH INCREMENTAL APPROACH!!"   , 0},
    {"readSBP",  504,    "SBPFILE",  0,  "Read symmetries to break statically from the file on the given path!!USED WITH INCREMENTAL APPROACH!!"   , 0},
    {"static",  505,    0,  0,  "Add static SBP !!USED WITH INCREMENTAL APPROACH!!"   , 0},

    {"propagate",  600,  0,  0,   "Also propagate information (as opposed to only exclude non-minimal solutions). !!USE WITH BACKTRACKING APPROACH!!", 0},
    {"maxDepth",  601,  "MAXDEPTH",  0,   "Define the maximum depth of the search tree during a partial minimality check. !!USE WITH BACKTRACKING APPROACH!!", 0},
    {"maxMC",  602,  "MAXMC",  0,   "Define the maximum number of nodes visited in the search tree during a partial minimality check. !!USE WITH BACKTRACKING APPROACH!!", 0},
    {0, 0, 0, 0, 0, 0},
};

static  int parse_opt(int key, char *arg, struct argp_state *state) {
    switch (key) {
        case 'n': {
            noEnum = true;
            break;
        }

        case 's': {
            int i = atoi(arg);
            if (i < 1) {
                argp_failure(state,1,0,"Problem size %d should be larger than zero.", i);
                break;
            }
            problem_size = i;
            break;
        }

        case 200:
        {
            int element;
            stringstream ss;
            ss<<arg;
            while (ss >> element)
            {
                diagonal.push_back(element);

                if (ss.peek() == ',')
                    ss.ignore();
            }
            if(int(diagonal.size())!=problem_size){
                argp_failure(state,1,0,"diagonal has length %lu different from problem size %d.", diagonal.size(),problem_size);
                break;
            }
            break;
        }
        case 201:
            indecomp = true;
            break;

        case 300:
            noCommander = true;
            break;
        case 301:
            smallerEncoding = true;
            break;
        case 302:
            useBit = true;
            break;
        case 303:
            oldBreakingClauses = true;
            break;
        case 400:
            checkSolutionInProp=true;
            break;
        case 401:
            propagateLiteralsCadical=true;
            break;
        case 402: {
            int i = atoi(arg);
            if (i < 1) {
                argp_failure(state,1,0,"Check frequency %d should be larger than zero.", i);
                break;
            }
            checkFreq=i;
            break;
        }
        case 403: {
            int i = atoi(arg);
            if (i < 1) {
                argp_failure(state,1,0,"Time limit %d should be larger than zero.", i);
                break;
            }
            timelimit=i;
            break;
        }
        case 404:
            solOutput = arg;
            break;
        case 'l':
            logOutput = arg;
            break;
        case 405:
            logging = atoi(arg);
            break;
        case 'p':
            allPart=true;
            break;
        case 'i':
            incrMincheck=true;
            break;
        case 500: {
            int i = atoi(arg);
            if (i < 1) {
                argp_failure(state,1,0,"Decision limit %d should be larger than zero.", i);
                break;
            }
            limDec=i;
            break;
        }
        case 501: {
            int i = atoi(arg);
            if (i < 1) {
                argp_failure(state,1,0,"Conflict limit %d should be larger than zero.", i);
                break;
            }
            limCon=i;
            break;
        }
        case 502: {
            int i = atoi(arg);
            if (i < 1) {
                argp_failure(state,1,0,"Clause length limit frequency %d should be larger than zero.", i);
                break;
            }
            limCls=i;
            break;
        }
        case 503:
            saveState=true;
            break;
        case 504:
            SBPPath=arg;
            break;
        case 505:
            staticSBP=true;
            break;
        case 506: {
            int i = atoi(arg);
            if (i < 1) {
                argp_failure(state,1,0,"SBP limit %d should be larger than zero.", i);
                break;
            }
            limSBP=i;
            break;
        }
        case 507: 
            oldSBP=true;
            break;
        case 600:
            propagateMincheck=true;
            break;
        case 601: {
            int i = atoi(arg);
            if (i < 1) {
                argp_failure(state,1,0,"Maximum depth %d should be larger than zero.", i);
                break;
            }
            maxDepth=i;
            break;
        }
        case 602: {
            int i = atoi(arg);
            if (i < 1) {
                argp_failure(state,1,0,"Maximum number of nodes visited %d should be larger than zero.", i);
                break;
            }
            maxMC=i;
            break;
        }
        case ARGP_KEY_END:
            if (state->argc<=1)
                printf("Using default settings.\n");
            break;
    }

    return 0;
}

int main(int argc, char **argv)
{
    struct argp argp = {options, parse_opt, doc, 0, 0, 0, 0};
    argp_parse(&argp, argc, argv, 0, 0, 0);

    if ((limDec>0||limCon>0||limCls>0||allPart)&&!incrMincheck) {
        printf("Limiting decisions and conflicts, or using the partial encoding can only be done with the incremental minimality check.\n");
        EXIT_UNWANTED_STATE
    }

    if ((maxDepth!=INT_MAX||maxMC!=INT_MAX)&&incrMincheck) {
        printf("Limiting depth and nodes visited can not be used with the incremental minimality check.\n");
        EXIT_UNWANTED_STATE
    }

    if (propagateMincheck&&incrMincheck) {
        printf("This feature is not implemented yet.\n");
        EXIT_UNWANTED_STATE
    }


    srand(static_cast<unsigned>(rseed));

    // ASSIGN DEFAULTS
    int t=0;
    for(int i=0; i<problem_size; i++)
        t+=i;
    t*=problem_size;

    string logFilePath;

    if(logOutput==""){
        logFilePath.append("size_");
        logFilePath.append(to_string(problem_size));
        logFilePath.append(".log");
    } else {

        logFilePath.append(logOutput);
        logFilePath.append(".log");
    }

    int old_stdout = dup(1);
    freopen(logFilePath.c_str(),"w",stdout);

    if (diagonal.empty()){
        using namespace std::chrono;
        auto start = steady_clock::now();

        vector<int> toPart;
        vector<vector<int>> parts;
        for(int i=0; i<problem_size; i++)
            toPart.push_back(i);
        part(problem_size, toPart, 0, parts);
        vector<vector<int>> diags;
        vector<int> d;
        for(int i=0; i<problem_size; i++)
            d.push_back(i);
        diags.push_back(d);
        d.clear();
        makeDiagonals(parts, diags);

        vector<int> numSols=vector<int>(diags.size(),0);

        size_t i;
        
        #pragma omp parallel for shared(numSols,i,t,diags) schedule(dynamic, 1) if(diags.size()>=20) 
        for(i=0; i<diags.size(); i++)
        {
            auto diag = diags[i];
            statistics stats;
            stats.start=steady_clock::now();

            cnf_t cnf;
            int nextFree = 1;

            auto cycset_lits = vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));
            auto geq_lits = vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));

            encodeEntries(&cnf, diag, nextFree, cycset_lits);

            if(staticSBP && !oldSBP)
                encodeOrder(&cnf, diag, nextFree, geq_lits, cycset_lits);

            YBEClauses(&cnf, nextFree, cycset_lits, diag);

            if(indecomp)
                enforceNoFixedEntries(&cnf, diag, cycset_lits);

            // check if zero literal
            for (const auto& clause : cnf)
            {
                for (auto lit : clause)
                    if (lit == 0)
                        EXIT_UNWANTED_STATE
            }

            CommonInterface *solver;

            int highestVariable = 0;
            for (const auto& clause : cnf)
            {
                for (auto lit : clause)
                    highestVariable = max(highestVariable, abs(lit));
            }

            solver = new CadicalSolver(cnf, highestVariable,diag, cycset_lits, geq_lits, stats);
            solver->solve();
            numSols[i]=solver->nModels;

            nextFreeVariable=max(nextFreeVariable,highestVariable);

            #pragma omp critical
            {
                printf("Diagonal: ");
                for(auto el :diag)
                    printf("%d-",el);
                printf("\n");
                printf("Total time diagonal: %f\n", (duration_cast<nanoseconds>(steady_clock::now()-stats.start).count()) / 1000000000.0);
                printf("---------------------------------------------------------\n");
            }
        }

        stdout = fdopen(old_stdout, "w");
        printf("Enumeration finished.\n");
        printf("Total time: %f\n", (duration_cast<nanoseconds>(steady_clock::now()-start).count()) / 1000000000.0);
        printf("Total models found: %d\n", accumulate(numSols.begin(),numSols.end(),0));
        printf("Log written to ");
        printf(logFilePath.c_str());
        printf(" in current working directory.\n");
        return 0;
    }

//else
    using namespace std::chrono;
    auto start = steady_clock::now();

    int totalModels=0;

    statistics stats;
    stats.start=steady_clock::now();

    cnf_t cnf;
    nextFreeVariable = 1;

    auto cycset_lits = vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));
    auto geq_lits = vector<vector<vector<lit_t>>>(problem_size, vector<vector<lit_t>>(problem_size, vector<lit_t>(problem_size, 0)));

    encodeEntries(&cnf, diagonal, nextFreeVariable, cycset_lits);

    if(staticSBP && !oldSBP)
        encodeOrder(&cnf, diagonal, nextFreeVariable, geq_lits, cycset_lits);
        
    YBEClauses(&cnf,nextFreeVariable,cycset_lits,diagonal);

    if(indecomp)
        enforceNoFixedEntries(&cnf, diagonal, cycset_lits);

    // check if zero literal
    for (const auto& clause : cnf)
    {
        for (auto lit : clause)
            if (lit == 0)
                EXIT_UNWANTED_STATE
    }

    CommonInterface *solver;

    int highestVariable = 0;
    for (const auto& clause : cnf)
    {
        for (auto lit : clause)
            highestVariable = max(highestVariable, abs(lit));
    }

    solver = new CadicalSolver(cnf, highestVariable, diagonal, cycset_lits, geq_lits, stats);
    solver->solve();
    totalModels=solver->nModels;

    printf("Diagonal: ");
    for(auto i :diagonal)
        printf("%d-",i);
    printf("\n");
    printf("Total time: %f\n", (duration_cast<nanoseconds>(steady_clock::now()-stats.start).count()) / 1000000000.0);
    printf("---------------------------------------------------------\n");

    /** reset cout buffer **/
    FILE *fp2 = fdopen(old_stdout, "w");
    fclose(stdout);
    stdout = fp2;
    *stdout = *fp2;
    close(old_stdout);

    printf("Enumeration finished.\n");
    printf("Total time: %f\n", (duration_cast<nanoseconds>(steady_clock::now()-start).count()) / 1000000000.0);
    printf("Total models found: %d\n", totalModels);
    printf("Log written to ");
    printf(logFilePath.c_str());
    printf(" in current working directory.\n");
    return 0;
}
