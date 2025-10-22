#include "domains.h"
#include "global.h"

bitdomain_t::bitdomain_t(){
  dom=vector<bool>();
  size=0;
  firstel=-1;
  numTrue=0;
}

bitdomain_t::bitdomain_t(int n,bool init){
  dom=vector<bool>(n,init);
  size=n;
  if(init){
    firstel=0;
    numTrue=size;
  } else {
    firstel=-1;
    numTrue=0;
  }
}

void bitdomain_t::set(int n){
  //printf("firstel before setting %d: %d\n",n,firstel);
  if(dom[n])
    return;

  dom[n]=true;
  numTrue+=1;
  if(firstel==-1 || n<firstel)
    firstel=n;
  //printf("firstel after setting %d: %d\n",n,firstel);
}

void bitdomain_t::reset(int n){
  //printf("firstel before resetting %d: %d\n",n,firstel);
  if(!dom[n])
    return;

  dom[n]=false;
  numTrue-=1;
  if(n==firstel){
    for(int i=n+1;i<size;i++){
      if(dom[i]){
        firstel=i;
        break;
      }
    }
    if(firstel==n)
      firstel=-1;
  }
  //printf("firstel after resetting %d: %d\n",n,firstel);
}

void bitdomain_t::set(){
  dom=vector<bool>(size,true);
  firstel=0;
  numTrue=size;
}

void bitdomain_t::reset(){
  dom=vector<bool>(size,false);
  firstel=-1;
  numTrue=0;
}

bool bitdomain_t::none(){
  return find_if(dom.begin(), dom.end(), [](bool x){return x;}) == dom.end();
}



vector<int> bitdomain_t::options(){
  vector<int> els = vector<int>();
  for(int j=0; j<size; j++){
    if(dom[j]){
      els.push_back(j);
    }
  }
  return els;
}

void bitdomain_t::print(){
  printf("{");
  for(int j =0; j<problem_size; j++){
    if(dom[j])
      printf("%d,",j);
  }
  printf("}");
}

bitdomains2_t::bitdomains2_t(){
  dom = vector<int>();
  chunk=0;
}
bitdomains3_t::bitdomains3_t(){
  dom = vector<int>();
  chunkr=0;
  chunkc=0;
}



bitdomains2_t::bitdomains2_t(bool init){
 chunk=problem_size+2;
 dom = vector<int>(chunk*problem_size,init);
 if(init){
  for(int i=0;i<problem_size;i++){
    dom[chunk*i]=0;
    dom[chunk*i+1]=problem_size;
  }
 } else {
    for(int i=0;i<problem_size;i++){
      dom[chunk*i]=-1;
    }
  }
}
bitdomains3_t::bitdomains3_t(bool init){
 chunkc=problem_size+2;
 chunkr=problem_size*chunkc;
 dom = vector<int>(chunkr*problem_size,init);
 if(init){
  for(int i=0;i<problem_size;i++){
    for(int j=0;j<problem_size;j++){
      dom[chunkr*j+chunkc*i]=0;
      dom[chunkr*j+chunkc*i+1]=problem_size;
    }
  }
 } else {
    for(int i=0;i<problem_size;i++){
      for(int j=0;j<problem_size;j++){
        dom[chunkr*j+chunkc*i]=-1;
      }
    }
  }
}



bitdomains2_t::~bitdomains2_t()= default;
bitdomains3_t::~bitdomains3_t()= default;



int bitdomains2_t::get(int idx) {
  if(numtrue(idx)==1){
    return firstel(idx);
  } else {
    return -1;
  }
}
int bitdomains3_t::get(int r, int c) {
  if(numtrue(r,c)==1){
    return firstel(r,c);
  } else {
    return -1;
  }
}



bool bitdomains2_t::get(int idx, int e) {
  if(numtrue(idx)!=0){
    return dom[chunk*idx+2+e]==1;
  } else {
    return false;
  }
}
bool bitdomains3_t::get(int r, int c, int e) {
  if(numtrue(r,c)!=0){
    return dom[chunkr*r+chunkc*c+2+e]==1;
  } else {
    return false;
  }
}



void bitdomains2_t::set(){
  dom = vector<int>(chunk*problem_size,true);
  for(int i=0;i<problem_size;i++){
    dom[chunk*i]=0;
    dom[chunk*i+1]=problem_size;
  }
}
void bitdomains3_t::set(){
  dom = vector<int>(chunkr*problem_size,1);
  for(int i=0;i<problem_size;i++){
    for(int j=0;j<problem_size;j++){
      dom[chunkr*j+chunkc*i]=0;
      dom[chunkr*j+chunkc*i+1]=problem_size;
    }
  }
}



void bitdomains2_t::reset(){
  dom = vector<int>(chunk*problem_size,false);
  for(int i=0;i<problem_size;i++){
    dom[chunk*i]=-1;
  }
}
void bitdomains3_t::reset(){
  dom = vector<int>(chunkr*problem_size,0);
  for(int i=0;i<problem_size;i++){
    for(int j=0;j<problem_size;j++){
      dom[chunkr*j+chunkc*i]=-1;
    }
  }
}



int bitdomains2_t::firstel(int e) {
  return dom[chunk*e];
}
int bitdomains3_t::firstel(int r, int c) {
  return dom[chunkr*r+chunkc*c];
}



int bitdomains2_t::numtrue(int e) {
  return dom[chunk*e+1];
}
int bitdomains3_t::numtrue(int r, int c) {
  return dom[chunkr*r+chunkc*c+1];
}



void bitdomains2_t::set(int e,int n){
  if(dom[chunk*e+2+n]==1)
    return;

  dom[chunk*e+2+n]=1;
  dom[chunk*e+1]+=1;
  int firstidx=firstel(e);
  if(firstidx==-1 || n<firstidx)
    dom[chunk*e]=n;
}
void bitdomains3_t::set(int r,int c,int n){
  if(dom[chunkr*r+chunkc*c+2+n]==1)
    return;

  dom[chunkr*r+chunkc*c+2+n]=1;
  dom[chunkr*r+chunkc*c+1]+=1;
  int firstidx=firstel(r,c);
  if(firstidx==-1 || n<firstidx)
    dom[chunkr*r+chunkc*c]=n;
}



void bitdomains2_t::reset(int e,int n){
  if(dom[chunk*e+2+n]==0)
    return;

  dom[chunk*e+2+n]=0;
  dom[chunk*e+1]-=1;
  int firstidx=firstel(e);
  if(n==firstidx){
    for(int i=n+1;i<problem_size;i++){
      if(dom[chunk*e+2+i]==1){
        dom[chunk*e]=i;
        break;
      }
    }
    if(dom[chunk*e]==n)
      dom[chunk*e]=-1;
  }
}
void bitdomains3_t::reset(int r, int c,int n){
  if(dom[chunkr*r+chunkc*c+2+n]==0)
    return;

  dom[chunkr*r+chunkc*c+2+n]=0;
  dom[chunkr*r+chunkc*c+1]-=1;
  int firstidx=firstel(r,c);
  if(n==firstidx){
    for(int i=n+1;i<problem_size;i++){
      if(dom[chunkr*r+chunkc*c+2+i]==1){
        dom[chunkr*r+chunkc*c]=i;
        break;
      }
    }
    if(dom[chunkr*r+chunkc*c]==n)
      dom[chunkr*r+chunkc*c]=-1;
  }
}



void bitdomains2_t::set(int e){
  for(int i=chunk*e+2;i<chunk*(e+1);i++){
    dom[i]=1;
  }
  dom[chunk*e]=0;
  dom[chunk*e+1]=problem_size;
}
void bitdomains3_t::set(int r, int c){
  for(int i=chunkr*r+chunkc*c+2;i<chunkr*r+chunkc*(c+1);i++){
    dom[i]=1;
  }
  dom[chunkr*r+chunkc*c]=0;
  dom[chunkr*r+chunkc*c+1]=problem_size;
}



void bitdomains2_t::reset(int e){
  for(int i=chunk*e+2;i<chunk*(e+1);i++){
    dom[i]=0;
  }
  dom[chunk*e] = -1;
  dom[chunk*e+1] = 0;
}
void bitdomains3_t::reset(int r, int c){
  for(int i=chunkr*r+chunkc*c+2;i<chunkr*r+chunkc*(c+1);i++){
    dom[i]=0;
  }
  dom[chunkr*r+chunkc*c]=-1;
  dom[chunkr*r+chunkc*c+1]=0;
}

bool bitdomains2_t::none(int e) {
  return numtrue(e)==0;
}
bool bitdomains3_t::none(int r, int c) {
  return numtrue(r, c)==0;
}


vector<int> bitdomains2_t::options(int e) {
  vector<int> els = vector<int>();
  /* if(rev){
    for(int j=problem_size-1; j>=0; j--){
      if(dom[chunk*e+j+2]==1){
        if(j==e){
          els.insert(els.begin(),e);
        } else {
          els.push_back(j);
        }
      }
    }
  } else {
    for(int j=0; j<problem_size; j++){
      if(dom[chunk*e+j+2]==1){
        if(j==e){
          els.insert(els.begin(),e);
        } else {
          els.push_back(j);
        }
      }
    }
  } */
  for(int j=0; j<problem_size; j++){
    if(dom[chunk*e+j+2]==1){
      els.push_back(j);
    }
  }
  return els;
}
vector<int> bitdomains3_t::options(int r, int c) {
  vector<int> els = vector<int>();
  for(int j=0; j<problem_size; j++){
    if(dom[chunkr*r+chunkc*c+j+2]==1){
      els.push_back(j);
    }
  }
  return els;
}



domInfo_t bitdomains2_t::analyzeDom(int e) {
  auto opts = options(e);
  if(opts.size()==0)
    return {false,false,-1};
  
  int min = *min_element(opts.begin(),opts.end());
  int max = *max_element(opts.begin(),opts.end());

  bool cons = (max-min+1) == opts.size();

  if(!cons)
    return {false,false,0};

  if(min==0) 
    return {true,true,max+1};
  else
  return {true,false,min};
}




void bitdomains2_t::print(){
  for(auto i = 0; i<problem_size; i++){
    printf("{");
    auto opt = options(i);
    for(auto o:opt){
      printf("%d,",o);
    }
    printf("}, ");
  }
  printf("\n");
}

void bitdomains3_t::print(){
  printf("TO DO\n");
}
