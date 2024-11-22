#include "minCheckCommon.h"
#include "global.h"
#include<tuple>
#include<algorithm>
#include<set>
#include<list>
#include<iterator>

void MinCheckCommon::addClauses(vector<int> &perm, int r, int c, bool old, bool prop){
    if(old)
        addClauses(perm,r,c);
    else
        addClausesProp(perm,r,c, prop);
}

bool MinCheckCommon::preCheck(cycle_set_t &cycset, vector<vector<vector<lit_t>>> &cycset_lits){
    bool isID = true;
    for(int i = 0; i<problem_size; i++){
        for(int j = 0; j<problem_size; j++){
            if(count(cycset.matrix[j].begin(), cycset.matrix[j].end(), i)>1){
                return true;
            } else if(cycset.bitdomains[i][j].numTrue==0){
                return true;
            }
            if(cycset.matrix[i][j]!=j)
                isID=false;
        }
    }
    return isID;
}


bool MinCheckCommon::permIsId(vector<int> &perm){
    for(int i=0; i<problem_size;i++){
        if(i==problem_size-1)
            return perm[i]==-1 || perm[i]==i;
        else if(perm[i]!=i)
            return false;
    }
}

int MinCheckCommon::permFullyDefinedCheck(vector<int> &perm, int i, int j){
    bool permId=true;

    if(permIsId(perm))
        return -1;

    vector<int> invperm = vector<int>(problem_size,-1);
    for(int r=0; r<problem_size; r++)
        invperm[perm[r]]=r;

    int fixes=0;
    for(int r = 0; r<problem_size;r++){
        for(int c=0; c<problem_size; c++){
            if(r<i || (r==i && c<j))
                continue;
            
            int minog = cycset.bitdomains[r][c].firstel;
            bool minOgFixed=cycset.bitdomains[r][c].numTrue==1;

            vector<int> permVal = cycset.bitdomains[perm[r]][perm[c]].options();

            if(perm[r]==r && perm[c]==c){

                if(minOgFixed){
                    int pv=permVal[0];
                    int inv=invperm[pv];
                    if(inv<minog){
                        addClauses(perm,r,c,oldBreakingClauses,false);
                    } else if (inv==minog){ 
                        continue;
                    } else {
                        return -1;
                    };
                } else {
                    vector<int> invpermvals=vector<int>();
                    for(auto p : permVal){
                        invpermvals.push_back(invperm[p]);
                    }
                    bool equals=false;
                    for(int i=0; i<permVal.size(); i++){
                        if(propagateMincheck && invpermvals[i]<permVal[i]){
                            addClauses(perm,r,c,oldBreakingClauses,true);
                        } else if(invpermvals[i]>permVal[i]){
                            return -1;
                        } else if(invpermvals[i]==permVal[i]){
                            equals=true;
                        }
                    }
                    if(!equals){
                        addClauses(perm,r,c,oldBreakingClauses,false);
                    }
                }
            } else {
                if(permVal.size()==1){
                    int pv=permVal[0];
                    int inv=invperm[pv];

                    if(inv<minog){
                        addClauses(perm,r,c,oldBreakingClauses,false);
                    } else if (minOgFixed && inv==minog){
                        continue;
                    } else if(propagateMincheck&&(inv==minog)) {
                        addClauses(perm,r,c,oldBreakingClauses,true);
                    } else {
                        return -1;
                    }
                } else {
                    vector<int> invpermvals=vector<int>();
                    for(auto p : permVal){
                        invpermvals.push_back(invperm[p]);
                    }
                    int max = *max_element(invpermvals.begin(),invpermvals.end());
                    
                    if (max<minog){
                        addClauses(perm,r,c,oldBreakingClauses,false);
                    } else if (!propagateMincheck && max<=minog){
                        continue;
                    } else if(propagateMincheck) {
                        if(max==minog){
                            addClauses(perm,r,c,oldBreakingClauses,true);
                        } else {
                            return -1;
                        } 
                    }  else {
                        return -1;
                    }
                }
            }
        }
    }
    return -1;
}

void MinCheckCommon::addClauses(vector<int> &perm, int r, int c)
{
    if(logging>0){
        printf("ADDING BREAKING CLAUSES %d %d\n",r,c);
        for(int i=0;i<problem_size;i++){
            printf("%d -> %d\n",i,perm[i]);
        }
    }

    vector<int> toAdd;
    vector<int> invperm=vector<int>(problem_size,-1);
        

    for(int i=0; i<problem_size; i++){
        if(perm[i]!=-1){
            invperm[perm[i]]=i;
        }
    }

    int index=problem_size-1;
    for(int ri=0;ri<=r;ri++){
        for(int ci=0;ci<=problem_size-1;ci++){
            if(diagPart && ri==ci)
                continue;
            int ogVal=cycset.matrix[ri][ci];
            
            if(ri==r && ci==c && ogVal!=-1){
                index=ogVal;
            }
            
            for(int i=problem_size-1; i>=0; i--){
                if(ri==r && ci==c && i==index)
                    goto endloopOld;
                if(diagPart && i==cycset.matrix[ri][ri])
                    continue;
                truth_vals og_asg = cycset.assignments[ri][ci][i];
                truth_vals perm_asg=cycset.assignments[perm[ri]][perm[ci]][perm[i]];
                if(ri!=perm[ri]||ci!=perm[ci]||i!=perm[i])
                {
                    if(og_asg==True_t){
                        toAdd.push_back(-cycset_lits[ri][ci][i]);
                        if(logging>1)
                            printf("-M_%d_%d_%d ",ri,ci,i); 
                    }
                        
                    if(perm_asg==False_t){
                        toAdd.push_back(cycset_lits[perm[ri]][perm[ci]][perm[i]]);
                        if(logging>1)
                            printf("M_%d_%d_%d ",perm[ri],perm[ci],perm[i]); 
                    }
                        
                }
            }
        }
    }

    endloopOld:
        vector<tuple<int,int>> permvals = vector<tuple<int,int>>();
        for(int pv : cycset.bitdomains[perm[r]][perm[c]].options()){
            permvals.push_back(tuple<int,int>{pv,invperm[pv]});
        }
        sort(permvals.begin(), permvals.end(), [](tuple<int,int>a,tuple<int,int>b){return get<1>(a)<=get<1>(b);});
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
            if(logging>1){
                printf("-M_%d_%d_%d ",r,c,og);
                printf("-M_%d_%d_%d\n",perm[r],perm[c],get<0>(permvals[0]));
            }
            throw toAdd;
        } else if(permValFixed){
            //vector<vector<int>> clss = vector<vector<int>>();
            vector<int> opts=cycset.bitdomains[r][c].options();
            toAdd.push_back(-cycset_lits[perm[r]][perm[c]][get<0>(permvals[0])]);
            if(logging>1){
                printf("-M_%d_%d_%d\n",perm[r],perm[c],get<0>(permvals[0]));
            }
            for(int i=0; i<permvals.size();i++){
                if(opts[i]>get<1>(permvals[0])){
                    //vector<int>cls=toAdd;
                    toAdd.push_back(-cycset_lits[r][c][opts[i]]);
                    if(logging>1){
                        printf(" and -M_%d_%d_%d\n",r,c,opts[i]);
                    }
                    throw toAdd;
                }
            }
        } else if(ogFixed) {
            toAdd.push_back(-cycset_lits[r][c][og]);
            if(logging>1){
                printf("-M_%d_%d_%d\n",r,c,og);
            }
            for(int i=0; i<permvals.size();i++){
                if(get<1>(permvals[i])<og){
                    toAdd.push_back(-cycset_lits[perm[r]][perm[c]][get<0>(permvals[i])]);
                    if(logging>1){
                        printf(" and -M_%d_%d_%d\n",perm[r],perm[c],get<0>(permvals[i]));
                    }
                    throw toAdd;
                }
            }
        } else {
            if(perm[r]==r && perm[c]==c){
                for(int i=0; i<permvals.size();i++){
                    if(get<1>(permvals[i])<get<0>(permvals[i]) ){
                        toAdd.push_back(-cycset_lits[perm[r]][perm[c]][get<0>(permvals[i])]);
                        if(logging>1){
                            printf(" and -M_%d_%d_%d\n",perm[r],perm[c],get<0>(permvals[i]));
                        }
                        throw toAdd;
                    }
                }
            } else {
                for(int i=0;i<problem_size;i++){
                    if(diagPart && i==cycset.matrix[r][r])
                        continue;
                    if(!cycset.bitdomains[r][c].dom[i]){
                        toAdd.push_back(cycset_lits[r][c][i]);
                        if(logging>1){
                            printf("M_%d_%d_%d",r,c,i);
                        }
                    }
                }
                if(logging>1){
                    printf("\n");
                }
                for(int i=0; i<permvals.size();i++){
                    if(get<1>(permvals[i])<og ){
                        toAdd.push_back(-cycset_lits[perm[r]][perm[c]][get<0>(permvals[i])]);
                        if(logging>1){
                            printf(" and -M_%d_%d_%d\n",perm[r],perm[c],get<0>(permvals[i]));
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
            if(smallerEncoding && lits[r].numtrue(c)==problem_size-2){
                for(int i=0;i<problem_size;i++){
                    if(i!=cycset.matrix[r][r]&& !lits[r].get(c,i)){
                        cls.push_back(-cycset_lits[r][c][i]);
                        if(logging>1)
                            printf("-M_%d_%d_%d\n",r,c,i);
                    }
                }
            } else if(!smallerEncoding && lits[r].numtrue(c)==problem_size-1){
                for(int i=0;i<problem_size;i++){
                    if(!lits[r].get(c,i)){
                        cls.push_back(-cycset_lits[r][c][i]);
                        if(logging>1)
                            printf("-M_%d_%d_%d\n",r,c,i);
                    }
                }
            } else if(lits[r].numtrue(c)>0){
                for(auto l : lits[r].options(c)){
                    cls.push_back(cycset_lits[r][c][l]);
                    if(logging>1)
                        printf("M_%d_%d_%d\n",r,c,l);
                }
            }
        }
    }
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


void MinCheckCommon::addClausesShort(vector<int> &perm, int r, int c)
{
    if(logging>0){
        printf("ADDING CLAUSES %d %d\n",r,c);
        for(int i=0;i<problem_size;i++){
            printf("%d -> %d\n",i,perm[i]);
        }
    }

    vector<int> cls=vector<int>();
    vector<bitdomains2_t> toAdd=vector<bitdomains2_t>(problem_size,bitdomains2_t(false));
    vector<int> invperm=vector<int>(problem_size,-1);
        

    for(int i=0; i<problem_size; i++){
        if(perm[i]!=-1){
            invperm[perm[i]]=i;
        }
    }


    for(int ri=0;ri<=r;ri++){
        for(int ci=0;ci<=problem_size-1;ci++){
            if(diagPart && ri==ci)
                continue;
            if(ri==r && ci==c)
                goto endloopOld;
            
            bool ogFixed=false;
            int og = cycset.matrix[ri][ci];
            if(og!=-1){
                ogFixed=true;
            } else {
                og = cycset.bitdomains[ri][ci].firstel;
            }

            if(perm[ri]!=ri || perm[ci]!=ci){
                vector<tuple<int,int>> permvals = vector<tuple<int,int>>();
                for(int pv : cycset.bitdomains[perm[ri]][perm[ci]].options()){
                    permvals.push_back(tuple<int,int>{pv,invperm[pv]});
                }
                sort(permvals.begin(), permvals.end(), [](tuple<int,int>a,tuple<int,int>b){return get<1>(a)<=get<1>(b);});
                bool permValFixed=permvals.size()==1;

                for(int i=0; i<get<1>(permvals.back());i++){
                    if(diagPart && i==cycset.matrix[ri][ri])
                        continue;
                    else if(!cycset.bitdomains[ri][ci].dom[i])
                        addToClause(ri,ci,i,toAdd);
                }

                for(int i=og+1; i<problem_size;i++){
                    if(diagPart && perm[i]==cycset.matrix[perm[ri]][perm[ri]])
                        continue;
                    else if(!cycset.bitdomains[perm[ri]][perm[ci]].dom[perm[i]])
                        addToClause(perm[ri],perm[ci],perm[i],toAdd);
                }
            } else {
                for(int i=0; i<problem_size;i++){
                    if(diagPart && i==cycset.matrix[ri][ri])
                        continue;
                    else if(invperm[i]>i && !cycset.bitdomains[ri][ci].dom[i]){
                        addToClause(ri,ci,i,toAdd);
                    }   
                }
            }
        }
    }

    endloopOld:

        vector<tuple<int,int>> permvals = vector<tuple<int,int>>();
        for(int pv : cycset.bitdomains[perm[r]][perm[c]].options()){
            permvals.push_back(tuple<int,int>{pv,invperm[pv]});
        }
        sort(permvals.begin(), permvals.end(), [](tuple<int,int>a,tuple<int,int>b){return get<1>(a)<=get<1>(b);});
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
                if(diagPart && i==cycset.matrix[r][r])
                    continue;
                else if(!cycset.bitdomains[r][c].dom[i])
                    addToClause(r,c,i,toAdd);
            }

            for(int i=get<1>(permvals.back())+1; i<problem_size;i++){
                if(diagPart && perm[i]==cycset.matrix[perm[r]][perm[r]])
                    continue;
                else if(!cycset.bitdomains[perm[r]][perm[c]].dom[perm[i]])
                    addToClause(perm[r],perm[c],perm[i],toAdd);
            }
            vector<int> cls = vector<int>();
            toClause(toAdd,cls);
            throw cls;
        //ELSE REFINE CYCLE SET
        } else if(permValFixed){
            printf("pfixed\n");
            vector<int> opts=cycset.bitdomains[r][c].options();
            for(int i=get<1>(permvals.back())+1; i<problem_size;i++){
                if(diagPart && perm[i]==cycset.matrix[perm[r]][perm[r]])
                    continue;
                else if(!cycset.bitdomains[perm[r]][perm[c]].dom[perm[i]])
                    addToClause(perm[r],perm[c],perm[i],toAdd);
            }
            for(int i=0; i<opts.size();i++){
                if(opts[i]>get<1>(permvals[0])){
                    cls.push_back(-cycset_lits[r][c][opts[i]]);
                    addToClause(r,c,opts[i],toAdd,true);
                    vector<int> cls = vector<int>();
                    toClause(toAdd,cls);
                    throw cls;
                }
            }
        } else if(ogFixed) {
            printf("ofixed\n");
            for(int i=0;i<og;i++){
                if(diagPart && i==cycset.matrix[r][r])
                    continue;
                if(!cycset.bitdomains[r][c].dom[i]){
                    addToClause(r,c,i,toAdd);
                }
            }
            for(int i=0; i<permvals.size();i++){
                if(get<1>(permvals[i])<og){
                    addToClause(perm[r],perm[c],get<0>(permvals[i]),toAdd,true);
                    vector<int> cls = vector<int>();
                    toClause(toAdd,cls);
                    throw cls;
                }
            }
        } else {
            if(perm[r]==r && perm[c]==c){
                for(int i=0; i<permvals.size();i++){
                    if(get<1>(permvals[i])<get<0>(permvals[i])){
                        addToClause(perm[r],perm[c],get<0>(permvals[i]),toAdd,true);
                        vector<int> cls = vector<int>();
                        toClause(toAdd,cls);
                        throw cls;
                    }
                }
            } else {
                if(og<=get<1>(permvals.back())){
                    printf("A\n");
                    for(int i=0;i<og;i++){
                        if(diagPart && i==cycset.matrix[r][r])
                            continue;
                        if(!cycset.bitdomains[r][c].dom[i]){
                            addToClause(r,c,i,toAdd);
                        }
                    }
                    for(int i=0; i<permvals.size();i++){
                        if(get<1>(permvals[i])<og){
                            addToClause(perm[r],perm[c],get<0>(permvals[i]),toAdd,true);
                            vector<int> cls = vector<int>();
                            toClause(toAdd,cls);
                            throw cls;
                        }
                    }
                } else if(og>=get<1>(permvals.front())) {
                    printf("B\n");
                    vector<int> opts=cycset.bitdomains[r][c].options();
                    for(int i=get<1>(permvals.back())+1; i<problem_size;i++){
                        if(diagPart && perm[i]==cycset.matrix[perm[r]][perm[r]])
                            continue;
                        else if(!cycset.bitdomains[perm[r]][perm[c]].dom[perm[i]])
                            addToClause(perm[r],perm[c],perm[i],toAdd);
                    }
                    for(int i=0; i<permvals.size();i++){
                        if(opts[i]>get<1>(permvals[0])){
                            cls.push_back(-cycset_lits[r][c][opts[i]]);
                            addToClause(r,c,opts[i],toAdd,true);
                            vector<int> cls = vector<int>();
                            toClause(toAdd,cls);
                            throw cls;
                        }
                    }
                }
            }
        }
}


void MinCheckCommon::addClausesProp(vector<int> &perm, int r, int c, bool prop)
{
    if(logging>0){
        printf("ADDING CLAUSES %d %d\n",r,c);
        for(int i=0;i<problem_size;i++){
            printf("%d -> %d\n",i,perm[i]);
        }
    }

    vector<int> cls=vector<int>();
    vector<bitdomains2_t> toAdd=vector<bitdomains2_t>(problem_size,bitdomains2_t(false));
    vector<int> invperm=vector<int>(problem_size,-1);
        

    for(int i=0; i<problem_size; i++){
        if(perm[i]!=-1){
            invperm[perm[i]]=i;
        }
    }


    for(int ri=0;ri<=r;ri++){
        for(int ci=0;ci<=problem_size-1;ci++){
            if(diagPart && ri==ci)
                continue;
            if(ri==r && ci==c)
                goto endloopOld;

            if(perm[ri]!=ri || perm[ci]!=ci){
                int minog=cycset.matrix[ri][ci];
                if(minog==-1){
                    minog = cycset.bitdomains[ri][ci].firstel;
                }

                vector<int> permvals = vector<int>();
                for(int pv : cycset.bitdomains[perm[ri]][perm[ci]].options()){
                    permvals.push_back(invperm[pv]);
                }
                int maxperm = *max_element(permvals.begin(),permvals.end());

                for(int i=0; i<minog;i++){
                    if(diagPart && i==cycset.matrix[ri][ri])
                        continue;
                    else if(!cycset.bitdomains[ri][ci].dom[i])
                        addToClause(ri,ci,i,toAdd);
                }

                for(int i=maxperm+1; i<problem_size;i++){
                    if(diagPart && perm[i]==cycset.matrix[perm[ri]][perm[ri]])
                        continue;
                    else if(!cycset.bitdomains[perm[ri]][perm[ci]].dom[perm[i]])
                        addToClause(perm[ri],perm[ci],perm[i],toAdd);
                }
            } else {
                for(int i=0; i<problem_size;i++){
                    if(diagPart && i==cycset.matrix[ri][ri])
                        continue;
                    else if(invperm[i]>i && !cycset.bitdomains[ri][ci].dom[i]){
                        addToClause(ri,ci,i,toAdd);
                    }   
                }
            }
        }
    }

    endloopOld:

        if(r!=perm[r]||c!=perm[c]){
            if(!prop){
                ////////////////////////
                // break unfixed cell //
                ////////////////////////
                int minog = cycset.matrix[r][c];
                if(minog==-1){
                    minog = cycset.bitdomains[r][c].firstel;
                }
                vector<int> permvals = vector<int>();
                for(int pv : cycset.bitdomains[perm[r]][perm[c]].options()){
                    permvals.push_back(invperm[pv]);
                }
                int maxperm = *max_element(permvals.begin(),permvals.end());

                for(int i=0; i<=maxperm;i++){
                    if(diagPart && i==cycset.matrix[r][r])
                        continue;
                    else if(!cycset.bitdomains[r][c].dom[i])
                        addToClause(r,c,i,toAdd);
                }

                for(int i=maxperm+1; i<problem_size;i++){
                    if(diagPart && perm[i]==cycset.matrix[perm[r]][perm[r]])
                        continue;
                    else if(!cycset.bitdomains[perm[r]][perm[c]].dom[perm[i]])
                        addToClause(perm[r],perm[c],perm[i],toAdd);
                }
                vector<int> cls = vector<int>();
                toClause(toAdd,cls);
                throw tuple<vector<int>,bool>({cls,prop});
            }else{
                ////////////////////////
                // prop  unfixed cell //
                ////////////////////////
                int minog = cycset.matrix[r][c];
                if(minog==-1){
                    minog = cycset.bitdomains[r][c].firstel;
                }

                vector<tuple<int,int>> permvals = vector<tuple<int,int>>();
                for(int pv : cycset.bitdomains[perm[r]][perm[c]].options()){
                    permvals.push_back(tuple<int,int>({pv,invperm[pv]}));
                }
                sort(permvals.begin(), permvals.end(), [](tuple<int,int>a,tuple<int,int>b){return get<1>(a)<=get<1>(b);});
                int maxperm = get<1>(permvals.back());

                if(permvals.size()!=1){
                    for(int i=0;i<minog;i++){
                        if(diagPart && i==cycset.matrix[r][r])
                            continue;
                        if(!cycset.bitdomains[r][c].dom[i]){
                            addToClause(r,c,i,toAdd);
                        }
                    }
                    for(int i=0; i<permvals.size();i++){
                        if(get<1>(permvals[i])<minog){
                            addToClause(perm[r],perm[c],get<0>(permvals[i]),toAdd,true);
                            vector<int> cls = vector<int>();
                            toClause(toAdd,cls);
                            throw tuple<vector<int>,bool>({cls,prop});
                        }
                    }
                } else {
                    vector<int> opts=cycset.bitdomains[r][c].options();
                    for(int i=maxperm+1; i<problem_size;i++){
                        if(diagPart && perm[i]==cycset.matrix[perm[r]][perm[r]])
                            continue;
                        else if(!cycset.bitdomains[perm[r]][perm[c]].dom[perm[i]])
                            addToClause(perm[r],perm[c],perm[i],toAdd);
                    }
                    for(int i=0; i<opts.size();i++){
                        if(opts[i]>maxperm){
                            addToClause(r,c,opts[i],toAdd,true);
                            vector<int> cls = vector<int>();
                            toClause(toAdd,cls);
                            throw tuple<vector<int>,bool>({cls,prop});
                        }
                    }
                }
                
            }
        } else {
            if(!prop){
                ////////////////////////
                //  break fixed cell  //
                ////////////////////////
                for(int i=0; i<problem_size;i++){
                    if(diagPart && i==cycset.matrix[r][r])
                        continue;
                    else if(invperm[i]>=i && !cycset.bitdomains[r][c].dom[i]){
                        addToClause(r,c,i,toAdd);
                    }   
                }
                vector<int> cls = vector<int>();
                toClause(toAdd,cls);
                throw tuple<vector<int>,bool>({cls,prop});
            }else{
                ////////////////////////
                //  prop fixed cell   //
                ////////////////////////
                for(int i=0; i<problem_size;i++){
                    if(diagPart && i==cycset.matrix[r][r])
                        continue;
                    else if(invperm[i]<i && cycset.bitdomains[r][c].dom[i]){
                        addToClause(r,c,i,toAdd,true);
                        vector<int> cls = vector<int>();
                        toClause(toAdd,cls);
                        throw tuple<vector<int>,bool>({cls,prop});
                    }   
                }
                
            }
        }
}
