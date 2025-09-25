/**
 * Implementation of common parts amongst all solvers
 */
#include "useful.h"
#include "global.h"
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
    if(!mincheck->preCheck(cycset)){
      mincheck->MinCheck(cycset);
      //checkMinimality(cycset,cycset_lits);
    }
  }
  catch (clause_t &c)
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
  catch (vector<clause_t> &cs)
  {
    //for(auto c : cs){
      stats.nClauses+=1LL;
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
  catch (tuple<clause_t,bool> cs)
  {
    if(get<1>(cs)){
      stats.nClauses+=1LL;
      stats.nPropClauses+=1LL;
    } else {
      stats.nSymBreakClauses+=1LL;
    }
    addClause(get<0>(cs),true);

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
    failed = true;
  }

  if(fullDefined && !failed){
    nModels++;
    if(!noEnum){
      fprintf(output,"Solution %d\n", nModels);
      fprintCycleSet(output, cycset);
    }
    vector<lit_t> clause;
    for (int i = 0; i < problem_size; i++)
      for (int j = 0; j < problem_size; j++)
      {
        if(i==j)
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
  
  if(!noEnum){
    fprintf(output,"Solution %d\n", nModels);
    fprintCycleSet(output, cycset);
  }

  // exclude current cycle set
  vector<lit_t> clause;
  for (int i = 0; i < problem_size; i++)
    for (int j = 0; j < problem_size; j++)
    {
      if(i==j)
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

void CommonInterface::printStatistics()
{
  printf("Time in propagator: %f\n", (stats.timePropagator));
  printf("Calls of propagator: %lld\n", stats.callsPropagator);

  printf("Time spent on minimality checks: %f\n", (stats.timeMinimalityCheck));
  printf("Number of minimality checks: %lld\n", (stats.callsFullCheck+stats.callsPartCheck));
  printf("Number of added symmetry breaking constraints: %lld\n", stats.nSymBreakClauses);

  printf("Time spent on partial minimality checks: %f\n", (stats.timePartMinimalityCheck));
  printf("Number of partial minimality checks: %lld\n", stats.callsPartCheck);
  printf("Number of partial minimality checks - symmetry breaking constraints added: %lld\n", stats.PartCheckSucc);
  printf("Number of partial minimality checks - nothing added: %lld\n", stats.PartCheckFail);
  printf("Time spent on partial minimality checks - symmetry breaking constraints added: %f\n", (stats.PartCheckSuccTime));
  printf("Time spent on partial minimality checks - nothing added: %f\n", (stats.PartCheckFailTime));

  printf("Time spent on complete minimality checks: %f\n", (stats.timeFullMinimalityCheck));
  printf("Number of complete minimality checks: %lld\n", stats.callsFullCheck);
  printf("Number of complete minimality checks - symmetry breaking constraints added: %lld\n", stats.FullCheckSucc);
  printf("Number of complete minimality checks - nothing added: %lld\n", stats.FullCheckFail);
  printf("Time spent on complete minimality checks - symmetry breaking constraints added: %f\n", (stats.FullCheckSuccTime));
  printf("Time spent on complete minimality checks - nothing added: %f\n", (stats.FullCheckFailTime));
  
  printf("Number of models: %d\n", nModels);
}

void CommonInterface::printStatistics(FILE *fp)
{
  fprintf(fp,"Time in propagator: %f\n", (stats.timePropagator));
  fprintf(fp,"Calls of propagator: %lld\n", stats.callsPropagator);

  fprintf(fp,"Time spent on minimality checks: %f\n", (stats.timeMinimalityCheck));
  fprintf(fp,"Number of minimality checks: %lld\n", (stats.callsFullCheck+stats.callsPartCheck));
  fprintf(fp,"Number of added symmetry breaking constraints: %lld\n", stats.nSymBreakClauses);

  fprintf(fp,"Time spent on partial minimality checks: %f\n", (stats.timePartMinimalityCheck));
  fprintf(fp,"Number of partial minimality checks: %lld\n", stats.callsPartCheck);
  fprintf(fp,"Number of partial minimality checks - symmetry breaking constraints added: %lld\n", stats.PartCheckSucc);
  fprintf(fp,"Number of partial minimality checks - nothing added: %lld\n", stats.PartCheckFail);
  fprintf(fp,"Time spent on partial minimality checks - symmetry breaking constraints added: %f\n", (stats.PartCheckSuccTime));
  fprintf(fp,"Time spent on partial minimality checks - nothing added: %f\n", (stats.PartCheckFailTime));

  fprintf(fp,"Time spent on complete minimality checks: %f\n", (stats.timeFullMinimalityCheck));
  fprintf(fp,"Number of complete minimality checks: %lld\n", stats.callsFullCheck);
  fprintf(fp,"Number of complete minimality checks - symmetry breaking constraints added: %lld\n", stats.FullCheckSucc);
  fprintf(fp,"Number of complete minimality checks - nothing added: %lld\n", stats.FullCheckFail);
  fprintf(fp,"Time spent on complete minimality checks - symmetry breaking constraints added: %f\n", (stats.FullCheckSuccTime));
  fprintf(fp,"Time spent on complete minimality checks - nothing added: %f\n", (stats.FullCheckFailTime));

  fprintf(fp,"Number of models: %d\n", nModels);
}

void CommonInterface::solve()
{
  // solve
  //printf("** Start solving\n");
  fflush(stdout);

  // get a solve handle
  auto assumps=vector<int>();
  solve(assumps);

  //printf("** Search finished\n");
  printStatistics();
}