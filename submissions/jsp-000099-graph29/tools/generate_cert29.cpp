#include <cstdint>
#include <cstdio>
#include <fstream>
#include <string>
#include <algorithm>
#include <cassert>
uint32_t a[29];uint64_t nodes;int pc(uint32_t x){return __builtin_popcount(x);}
void cert(uint32_t s,uint32_t u,int d,std::ostream &out);
void cert_body(uint32_t s,uint32_t u,int d,std::ostream &out){
 nodes++;
 if(pc(s|u)<7){out<<".small";return;}
 for(uint32_t t=s;t;t&=t-1){int v=__builtin_ctz(t);int lo=pc(a[v]&s),hi=pc(a[v]&(s|u));if(lo>d||hi<d){out<<"(.bad "<<v<<")";return;}}
 for(uint32_t t=s;t;t&=t-1){int v=__builtin_ctz(t);int lo=pc(a[v]&s),hi=pc(a[v]&(s|u));uint32_t change=a[v]&u;
  if(change && lo==d){out<<"(.empty "<<v<<" ";cert(s,u&~change,d,out);out<<")";return;}
  if(change && hi==d){out<<"(.fill "<<v<<" ";cert(s|change,u&~change,d,out);out<<")";return;}}
 for(uint32_t t=u;t;t&=t-1){int v=__builtin_ctz(t);if(pc(a[v]&s)>d||pc(a[v]&(s|u))<d){out<<"(.drop "<<v<<" ";cert(s,u&~(1u<<v),d,out);out<<")";return;}}
 assert(u);int v=__builtin_ctz(u),best=-1;
 for(uint32_t t=u;t;t&=t-1){int w=__builtin_ctz(t);int score=pc(a[w]&s);if(score>best){best=score;v=w;}}
 uint32_t bit=1u<<v;out<<"(.split "<<v<<" ";cert(s|bit,u^bit,d,out);out<<" ";cert(s,u^bit,d,out);out<<")";
}
int depth=0;
void cert(uint32_t s,uint32_t u,int d,std::ostream &out){
 bool checkpoint=(depth%4==0);
 if(checkpoint)out<<"(.checkpoint "<<s<<" "<<(s|u)<<" ";
 depth++;cert_body(s,u,d,out);depth--;
 if(checkpoint)out<<")";
}
int main(int argc,char**argv){std::ifstream f(argv[1]);std::string str;std::getline(f,str);assert(str[0]-63==29);int bit=0;for(int j=1;j<29;j++)for(int i=0;i<j;i++,bit++)if((str[1+bit/6]-63)&(1<<(5-bit%6))){a[i]|=1u<<j;a[j]|=1u<<i;}
 for(int d=0;d<29;d++){nodes=0;std::string p=std::string(argv[2])+"/Degree"+std::to_string(d)+".lean";std::ofstream out(p);out<<"import CheckpointCertificate\nset_option maxHeartbeats 0\nset_option maxRecDepth 10000\nnamespace Erdos82Finite\nopen RegularCertificate\ndef cert"<<d<<" : FastCert :=\n";cert(0,(1u<<29)-1,d,out);
 out<<"\n theorem checked"<<d<<" : fcheck 7 "<<d<<" 0 full cert"<<d<<" = true := by\n  decide +kernel\n\n theorem no_regular_"<<d<<" (T : Finset (Fin 29)) (h : 7 ≤ T.card) : ¬ RegularOn neighbors T "<<d<<" :=\n  fcheck_sound "<<d<<" cert"<<d<<" checked"<<d<<" T h\n\n#print axioms no_regular_"<<d<<"\nend Erdos82Finite\n";
 printf("d=%d nodes=%llu\n",d,(unsigned long long)nodes);}
}
