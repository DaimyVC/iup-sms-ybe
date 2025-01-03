#ifndef GLOBAL_H
#define GLOBAL_H

#include "useful.h"

extern int nextFreeVariable;

extern int problem_size;
extern int checkFreq;
extern int maxDepth;
extern int maxMC;
extern int limDec;
extern int limCon;
extern int logging;
extern int timelimit;
extern int limCls;
extern bool doFinalCheck;
extern bool useBit;
extern bool incrMincheck;
extern bool allPart;
extern bool noEnum;
extern bool propagateLiteralsCadical;
extern bool checkSolutionInProp;
extern bool smallerEncoding;
extern bool propagateMincheck;
extern bool oldBreakingClauses;
extern bool saveState;
extern bool readState;
extern bool noCommander;
extern string solOutput;


#define COUNT_ASSIGNED 0
#define ESTIMATE_SPACE 1

typedef struct
{
    chrono::_V2::steady_clock::time_point start;
    double timePropagator=0.0;
    double timeMinimalityCheck=0.0;
    long long callsPropagator=0;
    double timeFullMinimalityCheck = 0.0;
    long long callsFullCheck=0;
    long long FullCheckSucc=0;
    long long FullCheckFail=0;
    double FullCheckSuccTime=0.0;
    double FullCheckFailTime=0.0;
    double timePartMinimalityCheck = 0.0;
    long long callsPartCheck=0;
    long long PartCheckSucc=0;
    long long PartCheckFail=0;
    double PartCheckSuccTime = 0.0;
    double PartCheckFailTime = 0.0;
    long long nSymBreakClauses=0; // number of symmetry breaking clauses
    long long hyperclauses=0;
} statistics;

#endif
