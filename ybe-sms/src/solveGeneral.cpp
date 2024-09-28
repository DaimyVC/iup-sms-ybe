/**
 * Implementation of common parts amongst all solvers
 */
#include "useful.h"
#include "global.h"
#include "solve.h"
#include "solveGeneral.hpp"
#include "cadical.hpp"

typedef int lit_t;

bool CommonInterface::propagate()
{
  stats.callsPropagator+=1LL;
  auto start = steady_clock::now();

  bool res;

  if (checkSolutionInProp && (rand() % checkFreq == 0))
  {
    res=checkMin(false);
  }
  else
    res=true;
  
  stats.timePropagator += ((duration_cast<nanoseconds>(steady_clock::now()-start).count()) / 1000000000.0);;
  return res;
}

bool CommonInterface::checkMin(bool final)
{

  auto start = steady_clock::now();
  bool res = true;
  cycle_set_t cycset = getCycleSet();
  
  bool fullDefined = true;
  for(auto i = problem_size-1; i>=0; i--){
    for(auto j=problem_size-1; j>=0; j--){
        if(cycset.matrix[i][j]==-1){
          fullDefined = false;
          break;
        }
    }
    if(!fullDefined)
      break;
  }
  
  if(fullDefined){
    mincheck->complete=true;
    mincheck->final=true;
  } else {
    mincheck->complete=false;
    mincheck->final=final;
  }

  bool failed=false;
  
  try
  {
    if(!mincheck->preCheck(cycset,cycset_lits)){
      mincheck->MinCheck(cycset);
      //checkMinimality(cycset,cycset_lits);
    }
  }
  catch (clause_t c)
  {
    stats.nSymBreakClauses+=1LL;
    addClause(c,true);
    res=false;
    failed=true;
    if(mincheck->final){
      auto dur = ((duration_cast<nanoseconds>(steady_clock::now()-start).count()) / 1000000000.0);
      stats.FullCheckSuccTime += dur;
      stats.FullCheckSucc+=1LL;
    } else {
      auto dur = ((duration_cast<nanoseconds>(steady_clock::now()-start).count()) / 1000000000.0);
      stats.PartCheckSuccTime += dur;
      stats.PartCheckSucc+=1LL;
    }
  }
  catch (vector<clause_t> cs)
  {
    //for(auto c : cs){
      stats.nSymBreakClauses+=1LL;
      addClause(cs.front(),true);
    //}
    res=false;
    failed=true;
    if(mincheck->final){
      auto dur = ((duration_cast<nanoseconds>(steady_clock::now()-start).count()) / 1000000000.0);
      stats.FullCheckSuccTime += dur;
      stats.FullCheckSucc+=1LL;
    } else {
      auto dur = ((duration_cast<nanoseconds>(steady_clock::now()-start).count()) / 1000000000.0);
      stats.PartCheckSuccTime += dur;
      stats.PartCheckSucc+=1LL;
    }
  } 
  catch (LimitReachedException)
  {
    bool failed = true;
  }

  if(fullDefined && !failed && allModels){
    nModels++;
    fprintf(output,"Solution %d\n", nModels);
    fprintCycleSet(output, cycset);
    vector<lit_t> clause;
    for (int i = 0; i < problem_size; i++)
      for (int j = 0; j < problem_size; j++)
      {
        if(diagPart && i==j)
              continue;
        for (int k = 0; k < problem_size; k++)
        {
          if (cycset.assignments[i][j][k] == True_t){
            clause.push_back(-cycset_lits[i][j][k]);
          }
        }
      }
    addClause(clause, false);
    res=false;
    stats.FullCheckFail+=1LL;
    auto dur = ((duration_cast<nanoseconds>(steady_clock::now()-start).count()) / 1000000000.0);
    stats.FullCheckFailTime += dur;
  }

  if(res && !mincheck->final){
    stats.PartCheckFail+=1LL;
    auto dur = ((duration_cast<nanoseconds>(steady_clock::now()-start).count()) / 1000000000.0);
    stats.PartCheckFailTime += dur;
  }

  auto dur = ((duration_cast<nanoseconds>(steady_clock::now()-start).count()) / 1000000000.0);
  stats.timeMinimalityCheck += dur;
  if(mincheck->final){
    stats.timeFullMinimalityCheck+=dur;
    stats.callsFullCheck+=1LL;
  }
  else{
    stats.timePartMinimalityCheck+=dur;
    stats.callsPartCheck+=1LL;
  }
  return res;
}

bool CommonInterface::check()
{
  auto start = steady_clock::now();
  bool res=checkMin(true);

  stats.timePropagator += ((duration_cast<nanoseconds>(steady_clock::now()-start).count()) / 1000000000.0);
  

  if(!res)
    return false;


  cycle_set_t cycset = getCycleSet();

  nModels++;
  fprintf(output,"Solution %d\n", nModels);
  fprintCycleSet(output, cycset);

  if (allModels)
  {
    // exclude current cycle set
    vector<lit_t> clause;
    for (int i = 0; i < problem_size; i++)
      for (int j = 0; j < problem_size; j++)
      {
        if(diagPart && i==j)
              continue;
        for (int k = 0; k < problem_size; k++)
        {
          if (cycset.assignments[i][j][k] == True_t){
            clause.push_back(-cycset_lits[i][j][k]);
          }
        }
      }
    addClause(clause, false);
    return false;
  }
  return true;
}

void CommonInterface::printStatistics()
{
  printf("Time in propagator: %f\n", (stats.timePropagator));
  printf("Calls propagator: %lld\n", stats.callsPropagator);

  printf("Time in minimality check: %f\n", (stats.timeMinimalityCheck));
  printf("Calls minimality check: %lld\n", (stats.callsFullCheck+stats.callsPartCheck));
  printf("Number of symmetry breaking constraints: %lld\n", stats.nSymBreakClauses);

  printf("Time in minimality check -- Partial: %f\n", (stats.timePartMinimalityCheck));
  printf("Calls of part check: %lld\n", stats.callsPartCheck);
  printf("Calls of part check - sbc added: %lld\n", stats.PartCheckSucc);
  printf("Calls of part check - nothing added: %lld\n", stats.PartCheckFail);
  printf("Time of part check - sbc added: %f\n", (stats.PartCheckSuccTime));
  printf("Time of part check - nothing added: %f\n", (stats.PartCheckFailTime));

  printf("Time in minimality check -- Full: %f\n", (stats.timeFullMinimalityCheck));
  printf("Calls of full check: %lld\n", stats.callsFullCheck);
  printf("Calls of full check - sbc added: %lld\n", stats.FullCheckSucc);
  printf("Calls of full check - nothing added: %lld\n", stats.FullCheckFail);
  printf("Time of full check - sbc added: %f\n", (stats.FullCheckSuccTime));
  printf("Time of full check - nothing added: %f\n", (stats.FullCheckFailTime));
  if (allModels)
    printf("Number of models: %d\n", nModels);
}

void CommonInterface::solve()
{
  // solve
  printf("** Start solving\n");
  fflush(stdout);

  // get a solve handle
  int cubeCounter = 0;
  solve(vector<int>());

  printf("** Search finished\n");
  printStatistics();
}