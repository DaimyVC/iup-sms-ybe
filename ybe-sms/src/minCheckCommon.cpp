#include "minCheckCommon.h"
#include "global.h"
#include "transCheck.hpp"
#include<tuple>
#include<algorithm>
#include<iterator>

void MinCheckCommon::addClauses(const vector<int> &perm, int r, int c, bool old){
    counter.addPerm(perm, cycset, r, c);
    if(old)
        addClauses(perm,r,c);
    else
        addClausesShort(perm,r,c);
}

bool MinCheckCommon::preCheck(cycle_set_t &cycset){
    bool isID = true;
    for(int i = 0; i<problem_size; i++){
        for(int j = 0; j<problem_size; j++){
            if((count(cycset.matrix[j].begin(), cycset.matrix[j].end(), i)>1) || cycset.bitdomains[i][j].numTrue==0 ){
                return true;
            }
            if(cycset.matrix[i][j]!=j)
                isID=false;
        }
    }
    if(indecomp){     
        auto transCheck = TransitivityCheck();
        transCheck.preventDecomposable(cycset);
    }
    return isID;
}


bool MinCheckCommon::permIsId(const vector<int> &perm){
    for(int i=0; i<problem_size;i++){
        if(i==problem_size-1)
            return perm[i]==-1 || perm[i]==i;
        else if(perm[i]!=i)
            return false;
    }
    // can never happen
    return false;
}

int MinCheckCommon::permFullyDefinedCheck(vector<int> &perm, int i, int j){
    if(permIsId(perm))
        return -1;

    auto invperm = vector<int>(problem_size,-1);
    for(int r=0; r<problem_size; r++)
        invperm[perm[r]]=r;

    int fixes=0;
    for(auto& [r,c] : order.orderedCells){
        // if(r<i || (r==i && c<j))
        //     continue;
            
        int minog = cycset.bitdomains[r][c].firstel;
        bool minOgFixed=cycset.bitdomains[r][c].numTrue==1;

        vector<int> permVal = cycset.bitdomains[perm[r]][perm[c]].options();

        if(permVal.size()==1){
            int pv=permVal[0];
            int inv=invperm[pv];

            if(inv<minog){
                addClauses(perm,r,c,oldBreakingClauses);
            } else if (minOgFixed && inv==minog){
                continue;
            } else if(propagateMincheck&&(inv==minog)) {
                addClauses(perm,r,c,oldBreakingClauses);
            } else {
                break;
            }
        } else {
            auto invpermvals=vector<int>();
            for(auto p : permVal){
                invpermvals.push_back(invperm[p]);
            }
            int max = *max_element(invpermvals.begin(),invpermvals.end());
            
            if(max<minog){
                addClauses(perm,r,c,oldBreakingClauses);
            } else if (!propagateMincheck && max<=minog){
                continue;
            } else if(propagateMincheck) {
                if(perm[r]==r && perm[c]==c){
                    int maxsize = static_cast<int>(permVal.size());
                    for(int val=0; val<maxsize; val++){
                        if(invpermvals[val]<permVal[val])
                            addClauses(perm,r,c,oldBreakingClauses);
                    }
                    break;
                } else if(max==minog){
                    addClauses(perm,r,c,oldBreakingClauses);
                } else {
                    break;
                } 
            } else {
                break;
            }
        }
    }
    return -1;
}

void MinCheckCommon::addClauses(const vector<int> &perm, int r, int c)
{
    if(logging>0){
        printf("ADDING BREAKING CLAUSES %d %d\n",r,c);
        for(int i=0;i<problem_size;i++){
            printf("%d -> %d\n",i,perm[i]);
        }
    }

    vector<int> toAdd;
    auto invperm=vector<int>(problem_size,-1);
        

    for(int i=0; i<problem_size; i++){
        if(perm[i]!=-1){
            invperm[perm[i]]=i;
        }
    }

    int index=problem_size-1;
    for(auto& [ri,ci] : order.orderedCells){
        int ogVal=cycset.matrix[ri][ci];
        if(ri==r && ci==c && ogVal!=-1)
            index=ogVal;
        
        for(int i=problem_size-1; i>=0; i--){
            if(ri==r && ci==c && i==index)
                break;
            if(i==cycset.matrix[ri][ri])
                continue;
            truth_vals og_asg = cycset.assignments[ri][ci][i];
            truth_vals perm_asg=cycset.assignments[perm[ri]][perm[ci]][perm[i]];
            if(ri!=perm[ri]||ci!=perm[ci]||i!=perm[i])
            {
                if(og_asg==True_t){
                    toAdd.push_back(-cycset_lits[ri][ci][i]);
                    //fprintf(SBPout,"%d,%d,%d,%d;",-1,ri,ci,i);
                    if(logging>1)
                        printf("-M_%d_%d_%d ",ri,ci,i); 
                }
                    
                if(perm_asg==False_t){
                    toAdd.push_back(cycset_lits[perm[ri]][perm[ci]][perm[i]]);
                    //fprintf(SBPout,"%d,%d,%d,%d;",1,perm[ri],perm[ci],perm[i]);
                    if(logging>1)
                        printf("M_%d_%d_%d ",perm[ri],perm[ci],perm[i]); 
                }
                    
            }
        }
    }

    auto permvals = vector<tuple<int,int>>();
    permvals.reserve(problem_size);
    for(int pv : cycset.bitdomains[perm[r]][perm[c]].options()){
        permvals.emplace_back(pv,invperm[pv]);
    }
    sort(permvals.begin(), permvals.end(), [](const tuple<int,int> &a, const tuple<int,int> &b){return get<1>(a)<=get<1>(b);});
    bool permValFixed=permvals.size()==1;
    bool ogFixed=false;
    int og = cycset.matrix[r][c];
    if(og!=-1){
        ogFixed=true;
    } else {
        og = cycset.bitdomains[r][c].firstel;
    }

    if(ogFixed && permValFixed){
        toAdd.push_back(-cycset_lits[r][c][og]);
        toAdd.push_back(-cycset_lits[perm[r]][perm[c]][get<0>(permvals[0])]);
        //fprintf(SBPout,"%d,%d,%d,%d;",-1,r,c,og);
        //fprintf(SBPout,"%d,%d,%d,%d;",-1,perm[r],perm[c],get<0>(permvals[0]));
        if(logging>1){
            printf("-M_%d_%d_%d ",r,c,og);
            printf("-M_%d_%d_%d\n",perm[r],perm[c],get<0>(permvals[0]));
        }
        throw toAdd;
    } else if(permValFixed){
        //vector<vector<int>> clss = vector<vector<int>>();
        vector<int> opts=cycset.bitdomains[r][c].options();
        toAdd.push_back(-cycset_lits[perm[r]][perm[c]][get<0>(permvals[0])]);
        //fprintf(SBPout,"%d,%d,%d,%d;",-1,perm[r],perm[c],get<0>(permvals[0]));
        if(logging>1){
            printf("-M_%d_%d_%d\n",perm[r],perm[c],get<0>(permvals[0]));
        }
        int numPermvals=int(permvals.size());
        for(int i=0; i<numPermvals;i++){
            if(opts[i]>get<1>(permvals[0])){
                //vector<int>cls=toAdd;
                toAdd.push_back(-cycset_lits[r][c][opts[i]]);
                //fprintf(SBPout,"%d,%d,%d,%d;\n",-1,r,c,opts[i]);
                if(logging>1){
                    printf(" and -M_%d_%d_%d\n",r,c,opts[i]);
                }
                throw toAdd;
            }
        }
    } else if(ogFixed) {
        toAdd.push_back(-cycset_lits[r][c][og]);
        //fprintf(SBPout,"%d,%d,%d,%d;",-1,r,c,og);
        if(logging>1){
            printf("-M_%d_%d_%d\n",r,c,og);
        }
        for(auto & permval : permvals){
            if(get<1>(permval)<og){
                toAdd.push_back(-cycset_lits[perm[r]][perm[c]][get<0>(permval)]);
                //fprintf(SBPout,"%d,%d,%d,%d;\n",-1,perm[r],perm[c],get<0>(permval));
                if(logging>1){
                    printf(" and -M_%d_%d_%d\n",perm[r],perm[c],get<0>(permval));
                }
                throw toAdd;
            }
        }
    } else {
        if(perm[r]==r && perm[c]==c){
            for(auto & permval : permvals){
                if(get<1>(permval)<get<0>(permval) ){
                    toAdd.push_back(-cycset_lits[perm[r]][perm[c]][get<0>(permval)]);
                    //fprintf(SBPout,"%d,%d,%d,%d;\n",-1,perm[r],perm[c],get<0>(permval));
                    if(logging>1){
                        printf(" and -M_%d_%d_%d\n",perm[r],perm[c],get<0>(permval));
                    }
                    throw toAdd;
                }
            }
        } else {
            for(int i=0;i<problem_size;i++){
                if(i==cycset.matrix[r][r])
                    continue;
                if(!cycset.bitdomains[r][c].dom[i]){
                    toAdd.push_back(cycset_lits[r][c][i]);
                    //fprintf(SBPout,"%d,%d,%d,%d;",1,r,c,i);
                    if(logging>1){
                        printf("M_%d_%d_%d",r,c,i);
                    }
                }
            }
            if(logging>1){
                printf("\n");
            }
            for(auto & permval : permvals){
                if(get<1>(permval)<og ){
                    toAdd.push_back(-cycset_lits[perm[r]][perm[c]][get<0>(permval)]);
                    //fprintf(SBPout,"%d,%d,%d,%d;\n",-1,perm[r],perm[c],get<0>(permval));
                    if(logging>1){
                        printf(" and -M_%d_%d_%d\n",perm[r],perm[c],get<0>(permval));
                    }
                    throw toAdd;
                }
            }
        }
    }
}

void MinCheckCommon::toClause(vector<bitdomains2_t> &lits, vector<int> &cls){
    for(int r=0;r<problem_size;r++){
        for(int c=0;c<problem_size;c++){
            int numTrue = lits[r].numtrue(c);
            if(numTrue == 0)
                continue;

            //auto [consec, lessThan, val] = lits[r].analyzeDom(c);
            // if(consec && lessThan){
            //     printf("%d,%d < %d => %d\n",r,c,val,-1*geq_lits[r][c][val]);
            //     cls.push_back(-1*geq_lits[r][c][val]);
            // } else if (consec){
            //     printf("%d,%d >= %d => %d\n",r,c,val,geq_lits[r][c][val]);
            //     cls.push_back(geq_lits[r][c][val]);
            // } else 
            
            if(smallerEncoding && numTrue==problem_size-2){
                for(int i=0;i<problem_size;i++){
                    if(i!=cycset.matrix[r][r]&& !lits[r].get(c,i)){
                        cls.push_back(-cycset_lits[r][c][i]);
                        //fprintf(SBPout,"%d,%d,%d,%d;",-1,r,c,i);
                        if(logging>1)
                            printf("-M_%d_%d_%d\n",r,c,i);
                    }
                }
            } else if(!smallerEncoding && numTrue==problem_size-1){
                for(int i=0;i<problem_size;i++){
                    if(!lits[r].get(c,i)){
                        cls.push_back(-cycset_lits[r][c][i]);
                        //fprintf(SBPout,"%d,%d,%d,%d;",-1,r,c,i);
                        if(logging>1)
                            printf("-M_%d_%d_%d\n",r,c,i);
                    }
                }
            } else {
                for(auto l : lits[r].options(c)){
                    cls.push_back(cycset_lits[r][c][l]);
                    //fprintf(SBPout,"%d,%d,%d,%d;",1,r,c,l);
                    if(logging>1)
                        printf("M_%d_%d_%d\n",r,c,l);
                }
            }
        }
    }
    //fprintf(SBPout,"\n");
}

void MinCheckCommon::addToClause(int r, int c, int lit, vector<bitdomains2_t> &lits, bool neg=false){
    if(neg){
        for(int i=0;i<problem_size;i++){
            if(smallerEncoding){
                if(i!=lit && i!=cycset.matrix[r][r]){
                    lits[r].set(c,i);
                }
                if(i!=c && i!=cycset.matrix[c][c]){
                    lits[r].reset(i,lit);
                }
            }
            else {
                if(i!=lit){
                    lits[r].set(c,i);
                }
                if(i!=c){
                    lits[r].reset(i,lit);
                }
            }
        }
    } else {
        lits[r].set(c,lit);
    }
}


void MinCheckCommon::addClausesShort(const vector<int> &perm, int r, int c)
{
    if(logging>0){
        printf("ADDING CLAUSES %d %d\n",r,c);
        for(int i=0;i<problem_size;i++){
            printf("%d -> %d\n",i,perm[i]);
        }
    }

    auto toAdd=vector<bitdomains2_t>(problem_size,bitdomains2_t(false));
    auto invperm=vector<int>(problem_size,-1);
        

    for(int i=0; i<problem_size; i++){
        if(perm[i]!=-1){
            invperm[perm[i]]=i;
        }
    }

    for(auto& [ri,ci] : order.orderedCells){
        if(ri==r && ci==c)
            break;
            
        int og = cycset.matrix[ri][ci];
        if(og==-1){
            og = cycset.bitdomains[ri][ci].firstel;
        }

        if(perm[ri]!=ri || perm[ci]!=ci){
            auto permvals = vector<tuple<int,int>>();
            permvals.reserve(problem_size);
            for(int pv : cycset.bitdomains[perm[ri]][perm[ci]].options()){
                permvals.emplace_back(pv,invperm[pv]);
            }
            sort(permvals.begin(), permvals.end(), [](const tuple<int,int> &a, const tuple<int,int> &b){return get<1>(a)<=get<1>(b);});

            for(int i=0; i<get<1>(permvals.back());i++){
                if (i==cycset.matrix[ri][ri])
                    continue;
                else if(!cycset.bitdomains[ri][ci].dom[i])
                    addToClause(ri,ci,i,toAdd);
            }

            for(int i=og+1; i<problem_size;i++){
                if(perm[i]==cycset.matrix[perm[ri]][perm[ri]])
                    continue;
                else if(!cycset.bitdomains[perm[ri]][perm[ci]].dom[perm[i]])
                    addToClause(perm[ri],perm[ci],perm[i],toAdd);
            }
        } else {
            for(int i=0; i<problem_size;i++){
                if(i==cycset.matrix[ri][ri])
                    continue;
                else if(invperm[i]>i && !cycset.bitdomains[ri][ci].dom[i]){
                    addToClause(ri,ci,i,toAdd);
                }   
            }
        }
    }

    auto permvals = vector<tuple<int,int>>();
    permvals.reserve(problem_size);
    for(int pv : cycset.bitdomains[perm[r]][perm[c]].options()){
        permvals.emplace_back(pv,invperm[pv]);
    }
    sort(permvals.begin(), permvals.end(), [](const tuple<int,int> &a, const tuple<int,int> &b){return get<1>(a)<=get<1>(b);});
    bool permValFixed=permvals.size()==1;
    bool ogFixed=false;
    int og = cycset.matrix[r][c];
    if(og!=-1){
        ogFixed=true;
    } else {
        og = cycset.bitdomains[r][c].firstel;
    }

    if(get<1>(permvals.back())<og){
        //PERM IS A WITNESS OF NON-MINIMALITY
        for(int i=0; i<og;i++){
            if(i==cycset.matrix[r][r])
                continue;
            else if(!cycset.bitdomains[r][c].dom[i])
                addToClause(r,c,i,toAdd);
        }

        for(int i=get<1>(permvals.back())+1; i<problem_size;i++){
            if(perm[i]==cycset.matrix[perm[r]][perm[r]])
                continue;
            else if(!cycset.bitdomains[perm[r]][perm[c]].dom[perm[i]])
                addToClause(perm[r],perm[c],perm[i],toAdd);
        }
        auto cls = vector<int>();
        toClause(toAdd,cls);
        throw cls;
    //ELSE REFINE CYCLE SET
    } else if(permValFixed){
        vector<int> opts=cycset.bitdomains[r][c].options();
        for(int i=get<1>(permvals.back())+1; i<problem_size;i++){
            if(perm[i]==cycset.matrix[perm[r]][perm[r]])
                continue;
            else if(!cycset.bitdomains[perm[r]][perm[c]].dom[perm[i]])
                addToClause(perm[r],perm[c],perm[i],toAdd);
        }
        for(int opt : opts){
            if(opt>get<1>(permvals[0])){
                addToClause(r,c,opt,toAdd,true);
                auto cls = vector<int>();
                toClause(toAdd,cls);
                throw cls;
            }
        }
    } else if(ogFixed) {
        for(int i=0;i<og;i++){
            if(i==cycset.matrix[r][r])
                continue;
            if(!cycset.bitdomains[r][c].dom[i]){
                addToClause(r,c,i,toAdd);
            }
        }
        for(auto & permval : permvals){
            if(get<1>(permval)<og){
                addToClause(perm[r],perm[c],get<0>(permval),toAdd,true);
                auto cls = vector<int>();
                toClause(toAdd,cls);
                throw cls;
            }
        }
    } else {
        if(perm[r]==r && perm[c]==c){
            for(auto & permval : permvals){
                if(get<1>(permval)<get<0>(permval)){
                    addToClause(perm[r],perm[c],get<0>(permval),toAdd,true);
                    auto cls = vector<int>();
                    toClause(toAdd,cls);
                    throw cls;
                }
            }
        } else {
            if(og<=get<1>(permvals.back())){
                for(int i=0;i<og;i++){
                    if(i==cycset.matrix[r][r])
                        continue;
                    if(!cycset.bitdomains[r][c].dom[i]){
                        addToClause(r,c,i,toAdd);
                    }
                }
                for(auto & permval : permvals){
                    if(get<1>(permval)<og){
                        addToClause(perm[r],perm[c],get<0>(permval),toAdd,true);
                        auto cls = vector<int>();
                        toClause(toAdd,cls);
                        throw cls;
                    }
                }
            } else if(og>=get<1>(permvals.front())) {
                vector<int> opts=cycset.bitdomains[r][c].options();
                for(int i=get<1>(permvals.back())+1; i<problem_size;i++){
                    if(perm[i]==cycset.matrix[perm[r]][perm[r]])
                        continue;
                    else if(!cycset.bitdomains[perm[r]][perm[c]].dom[perm[i]])
                        addToClause(perm[r],perm[c],perm[i],toAdd);
                }
                int numPermVals = int(permvals.size());
                for(int i=0; i<numPermVals;i++){
                    if(opts[i]>get<1>(permvals[0])){
                        addToClause(r,c,opts[i],toAdd,true);
                        auto cls = vector<int>();
                        toClause(toAdd,cls);
                        throw cls;
                    }
                }
            }
        }
    }
}