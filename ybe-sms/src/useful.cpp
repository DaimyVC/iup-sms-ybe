#include "useful.h"
#include "global.h"

void printCycleSet(const cycle_set_t &cycset)
{
    for (auto row : cycset.matrix)
    {
      for (auto value : row)
        printf("%d ", value);
      printf("\n");
    }
}

void fprintCycleSet(FILE *stream, const cycle_set_t &cycset)
{
    for (auto row : cycset.matrix)
    {
      for (auto value : row)
        fprintf(stream, "%d ", value);
      fprintf(stream, "\n");
    }
}

void printPartiallyDefinedCycleSet(const cycle_set_t &cycset)
{
    for (auto row : cycset.matrix)
    {
      for (auto value : row)
      {
        if (value<0)
        {
          printf("* ");
        } 
        else
        {
          printf("%d ", value);
        }
      }
      printf("\n");
    }
}

void printDomains(const cycle_set_t &cycset)
{
    for (auto row : cycset.bitdomains)
    {
      for (auto dom : row)
      {
        dom.print();
        printf("\t");
      }
      printf("\n");
    }
}

void printAssignments(const cycle_set_t &cycset)
{
    for (int i=0; i<problem_size; i++)
    {
      printf("ROW %d: ",i);
      for (int j=0; j<problem_size; j++)
      {
        for (int k=0; k<problem_size; k++){
          if(cycset.assignments[i][j][k]==True_t){
            printf("1 ");
          } else if (cycset.assignments[i][j][k]==False_t){
            printf("0 ");
          } else {
            printf("* ");
          }
        }
        printf("\t");
      }
      printf("\n");
    }
}

void printCnf(cnf_t *cnf)
{
  for(auto cl : *cnf)
  {
    for(auto lit: cl)
      printf("%d ", lit);
    printf("\n\n");
  }
}

/* https://stackoverflow.com/questions/22988674/partition-of-an-integer-number-of-partitions */
void part(int n, vector<int>& v, int level, vector<vector<int>>& parts){
    if(n<1)
        return ;
    v[level]=n;
    vector<int> p;
    for(int i=0; i<=level; i++)
      if(v[i]!=1)
        p.push_back(v[i]);
    if(p.size() != 0)
      parts.push_back(p);
    
    int first=(level==0) ? 1 : v[level-1];

    for(int i=first;i<=n/2;i++){
        v[level]=i;
        part(n-i, v, level+1, parts);
    }
}

void makeDiagonals(vector<vector<int>>& parts, vector<vector<int>>& permutations)
{
  vector<vector<vector<int>>> cycles;
  for(size_t i = 0; i<parts.size(); i++)
  {
    vector<int> part;
    if(parts[i].size()==1)
    {
      for(int j=0; j<parts[i][0]; j++)
        part.push_back(j);
      cycles.push_back(vector<vector<int>>{part});
      part.clear();
    }
    else
    {
      int toAdd=0;
      vector<vector<int>> cycs;
      for(size_t j=0; j<parts[i].size();j++)
      {
        for(int k=0; k<parts[i][j]; k++)
        {
          part.push_back(k+toAdd);
        }
        cycs.push_back(part);
        part.clear();
        toAdd+=parts[i][j];
      }
      cycles.push_back(cycs);
      cycs.clear();
    }
  }

  vector<int> perm=vector<int>();
  for(auto part : cycles)
  {
    for(int j=0; j<problem_size; j++)
      perm.push_back(j);
    for(auto p : part)
    {
      for(size_t i = 0; i<p.size()-1; i++)
        perm[p[i]]=p[i+1];
      perm[p[p.size()-1]]=p[0];
    }
    permutations.push_back(perm);
    perm.clear();
  }
}

vector<vector<int>> permToCyclePerm(vector<int> &perm){
  vector<vector<int>> cycles;
  vector<int> all = vector<int>(problem_size,-1);
  iota(all.begin(),all.end(),0);
  
  while(all.size()!=0){
    int i = *min_element(all.begin(),all.end());
    vector<int> cycle=vector<int>();
    while (find(cycle.begin(),cycle.end(),i)==cycle.end()){
      cycle.push_back(i);
      all.erase(find(all.begin(),all.end(),i));
      i=perm[i];
    }
    cycles.push_back(cycle);
  }
  return cycles;
}

void cycleToParts(vector<vector<int>> &perm, vector<int> &elOrd, vector<bool> &part){
  vector<bitdomain_t> parts = vector<bitdomain_t>(problem_size,bitdomain_t(problem_size,false));
  for(auto cyc : perm){
    int len = cyc.size();
    if(len!=0){
      for(int el : cyc)
        parts[len-1].set(el);
    }
  }

  parts.erase(
    remove_if(
      parts.begin(),
      parts.end(), 
      [](bitdomain_t d){return d.none();}),
      parts.end()
  );

  vector<vector<int>> mins = vector<vector<int>>(parts.size(),vector<int>(2,0));
  
  for(int i=0; i<parts.size();i++){
    mins[i][1]=i;
    //mins[i][0]=*min_element(parts[i].dom.begin(),parts[i].dom.end());
    mins[i][0]=parts[i].firstel;
  }

  sort(mins.begin(),mins.end(),[](vector<int>el1,vector<int>el2){return el1[0]<el2[0];});

  for(auto el : mins){
    bool first=true;
    for (int i = parts[el[1]].firstel; i < problem_size && i!=-1; i++){
      if(!parts[el[1]].dom[i])
        continue;
      else {
        if(first){
          part.push_back(true);
          first=false;
        } else 
          part.push_back(false);
        elOrd.push_back(i);
      }     
    }
  }
}

cyclePerm_t::cyclePerm_t(){ };

cyclePerm_t::cyclePerm_t(vector<int> perm){
  auto cycles = permToCyclePerm(perm);
  diag=perm;
  int index = 0;
  for(auto cyc : cycles){
    bool first=true;
    for(int el : cyc){
      if(first){
        part.push_back(cyc.size());
        first=false;
      }
      else{
        part.push_back(0);
      }
      element.push_back(el);
    }
  }

}

void cyclePerm_t::print(){
  for(auto i : element){
    printf("%d , ", i);
  }
  printf("\n");
  for(auto i : part){
    printf("%d , ", i);
  }
  printf("\n");
}

vector<int> cyclePerm_t::cycle(int el){
  vector<int> options;
  int p=0;
  for(int i=0; i<=el; i++){
    if(part[i]>0)
      p=i;
  }
  if(p==el && (p==problem_size-1 || part[p+1]>0)){
    options.push_back(el);
  } else {
    for(int i=el; i<problem_size; i++){
      if(i!=p && part[i]>0)
        break;
      options.push_back(i);
    }
    for(int i=p; i<el; i++){
      options.push_back(i);
    }
  }
  return options;
}

int cyclePerm_t::permOf(int el){
  if(el+1>=problem_size || part[el+1]>0){
    for(int i = el; i>=0; i--){
      if(part[i]>0){
        return element[i];
      }
    }
  } else
    return element[el+1];
}

int cyclePerm_t::invPermOf(int el){
  if(el-1<0 || part[el]>0){
    for(int i = el; i>=0; i++){
      if(part[i]>0){
        return element[i-1];
      }
    }
  } else
    return element[el-1];
}

pperm_plain::pperm_plain(){
}

pperm_plain::~pperm_plain(){
  /* delete[]&element;
  delete[]&part; */
}

pperm_plain::pperm_plain(vector<int> perm){
  auto cyc = permToCyclePerm(perm);
  cycleToParts(cyc, element, part);
}

void pperm_plain::print(){
  for(auto i : element){
    printf("%d , ", i);
  }
  printf("\n");
  for(auto i : part){
    printf("%d , ", i ? 1 : 0);
  }
  printf("\n");
}

bool pperm_plain::fixed(int el){
  if(el==problem_size-1){
    return part[el];
  } else {
    return (part[el]&&part[el+1]);
  }
}

bool pperm_plain::fullDefined(){
  for(int i=0; i<problem_size; i++){
    if(!fixed(i))
      return false;
  }
  return true;
}

bool pperm_plain::fix(int el, int img){
  int iperm = invPermOf(img);
  if(fixed(el) || (iperm!=-1 && fixed(iperm))){
    return element[el]==img;
  }
  
  if(element[el]!=img){
    int swp = find(element.begin(),element.end(),img)-element.begin();
    swap(element[el],element[swp]);
  }
        
  if(el+1<=problem_size-1)
      part[el+1]=true;
  return true;
}

int pperm_plain::permOf(int el){
  if(fixed(el)){
    return element[el];
  } else
    return -1;
}

int pperm_plain::invPermOf(int el){
  int invEl = find(element.begin(),element.end(),el)-element.begin();
  if(fixed(invEl)){
    return invEl;
  } else
    return -1;
}

vector<int> pperm_plain::getPerm(){
  return element;
}

shared_ptr<pperm_common> pperm_plain::copyPerm(){
  return make_shared<pperm_plain>(pperm_plain(*this));
}

vector<int> pperm_plain::options(int el){
  vector<int> options;
  int p=0;
  for(int i=0; i<=el; i++){
    if(part[i]==true)
      p=i;
  }

  if(p==el && (p==problem_size-1 || part[p+1]==true)){
    options.push_back(element[el]);
  } else {
    for(int i=el; i<problem_size; i++){
      if(i!=p && part[i]==true)
        break;
      options.push_back(element[i]);
    }
    for(int i=p; i<el; i++){
      options.push_back(element[i]);
    }
  }
  /* sort(options.begin(),options.end());
  if(rev)
    reverse(options.begin(),options.end());
  auto indp = find(options.begin(),options.end(),p);
  if(indp!=options.end())
    swap(*indp,*options.begin()); */
  return options;
}

vector<int> pperm_plain::invOptions(int el){
  vector<int> options;
  int p=0;
  int ind=0;
  for(int i=0; i<problem_size; i++){
    if(part[i]==true)
      p=i;
    if(element[i]==el){
      ind=i;
      break;
    }
  }

  if(p==ind && (p==problem_size-1 || part[p+1]==true)){
    options.push_back(ind);
  } else {
    for(int i=ind; i<problem_size; i++){
      if(i!=p && part[i]==true)
        break;
      options.push_back(i);
    }
    for(int i=p; i<ind; i++){
      options.push_back(i);
    }
  }
  /* sort(options.begin(),options.end());
  if(rev)
    reverse(options.begin(),options.end());
  auto indp = find(options.begin(),options.end(),p);
  if(indp!=options.end())
    swap(*indp,*options.begin()); */
  return options;
}

vector<pperm_bit> combinePerms(vector<pperm_bit> &perms){
  int numPerms = perms.size();
  for(int i=0; i<numPerms; i++){
    for(int j=0; j<numPerms; j++){
      if(i==j)
        continue;
      int totalDiffs = 0;
      int diffIndex = -1;
      for(int k=0; k<problem_size;k++){
        for(int l=0; l<problem_size; l++){
          if(perms[i].info.get(k,l)!=perms[j].info.get(k,l)){
            totalDiffs+=1;
            diffIndex=k;
          }
        }
      }
      if(totalDiffs==1){
        for (std::size_t k=0; k<problem_size; ++k){
          perms[i].info.dom[perms[i].info.chunk*diffIndex+2+k]=perms[i].info.dom[perms[i].info.chunk*diffIndex+2+k]^perms[j].info.dom[perms[j].info.chunk*diffIndex+2+k];
        }
        perms.erase(perms.begin()+j);
      } 
    }
  }
  return perms;
}

pperm_bit::pperm_bit(vector<int> perm){
  auto cyc = permToCyclePerm(perm);
  vector<bitdomain_t> parts = vector<bitdomain_t>(problem_size,bitdomain_t(problem_size,false));

  for(auto c : cyc){
    int len = c.size();
    if(len!=0){
      for(int el : c)
        parts[len-1].set(el);
    }
  }

  parts.erase(
    remove_if(
      parts.begin(),
      parts.end(), 
      [](bitdomain_t d){return d.none();}),
      parts.end()
  );

  info = bitdomains2_t(false);
  
  for(int i=0; i<parts.size();i++){
    if(!parts[i].none()){
        vector<int> opts=parts[i].options();
        for(int j : opts){
          info.dom[info.chunk*j]=parts[i].firstel;
          info.dom[info.chunk*j+1]=parts[i].numTrue;
          int l=2;
          for(auto k : parts[i].dom)
            info.dom[j*info.chunk+(l++)]=k;
        }
    }
  }
}
pperm_bit::pperm_bit(){
}
pperm_bit::~pperm_bit(){
}
shared_ptr<pperm_common> pperm_bit::copyPerm(){
  return make_shared<pperm_bit>(pperm_bit(*this));
}

int pperm_bit::permOf(int p){
  if(fixed(p)){
    return info.firstel(p);
  } else
    return -1;
}

vector<int> pperm_bit::options(int p){
  auto options = info.options(p);
  return options;
}

vector<int> pperm_bit::invOptions(int p){
  vector<int> options = vector<int>();
  for(int i = 0; i<problem_size; i++){
    if(info.get(i,p))
      options.push_back(i);
  }
  
  return options;
}

int pperm_bit::invPermOf(int p){
  for(int i=0; i<problem_size; i++){
    if(permOf(i)==p)
      return i;
  }
  return -1;
}
bool pperm_bit::fixed(int p){
  return info.numtrue(p)==1;
}
bool pperm_bit::fix(int p, int pp){
  if(!info.get(p,pp))
    return false;

  for (int i=0;i<problem_size;i++) {
    if(i==p){
      info.reset(i);
      info.set(i,pp);
    } else {
      info.reset(i,pp);
      if(info.none(i))
        return false;
    }
  }
  return true;
}
void pperm_bit::print(){
  info.print();
}
bool pperm_bit::fullDefined(){
  for(int i=0; i<problem_size; i++){
    if(!fixed(i))
      return false;
  }
  return true;
}
vector<int> pperm_bit::getPerm(){
  vector<int> perm = vector<int>(problem_size,-1);
  for(int i=0; i<problem_size; i++){
    if(this->fixed(i))
      perm[i]=info.firstel(i);
    else
      perm[i]=-1;
  }
  return perm;
}

/* void pperm_bit::set(int e,int n){
  if(info[(problem_size+3)*e+3+n]==1)
    return;

  info[(problem_size+3)*e+3+n]=1;
  info[(problem_size+3)*e+2]+=1;
  int firstel=info[(problem_size+3)*e+1];
  if(firstel==-1 || n<firstel)
    info[(problem_size+3)*e+1]=n;
}
void pperm_bit::reset(int e,int n){
  if(info[(problem_size+3)*e+3+n]==0)
    return;

  info[(problem_size+3)*e+3+n]=0;
  info[(problem_size+3)*e+2]-=1;
  int firstel=info[(problem_size+3)*e+1];
  if(n==firstel){
    for(int i=n+1;i<problem_size;i++){
      if(info[(problem_size+3)*e+3+i]==1){
        info[(problem_size+3)*e+1]=i;
        break;
      }
    }
    if(info[(problem_size+3)*e+1]==n)
      info[(problem_size+3)*e+1]=-1;
  }
}
void pperm_bit::set(int e){
  for(int i=0;i<problem_size;i++)
    info[(problem_size+3)*e+3+i]=1;
  info[(problem_size+3)*e+1]=0;
  info[(problem_size+3)*e+2]=problem_size;
}
void pperm_bit::reset(int e){
  for(int i=0;i<problem_size;i++)
    info[(problem_size+3)*e+3+i]=0;
  info[(problem_size+3)*e+1]=-1;
  info[(problem_size+3)*e+2]=0;
}
bool pperm_bit::none(int e){
  return find_if(info.begin()+(problem_size+3)*e+3, info.begin()+(problem_size+3)*(e+1), [](bool x){return x==1;}) == info.begin()+(problem_size+3)*(e+1);
}
void pperm_bit::print(int e){
  printf("ToDo\n");
}*/