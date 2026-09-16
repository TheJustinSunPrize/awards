#include <cstdint>
#include <cstdio>
#include <chrono>
#include <fstream>
#include <string>
#include <vector>
#include <cassert>
int main(int argc,char**argv){
 std::ifstream f(argv[1]);std::string s;std::getline(f,s);int n=s[0]-63;assert(n==29);
 std::vector<uint32_t>a(n);int bit=0;
 for(int j=1;j<n;j++)for(int i=0;i<j;i++,bit++)if((s[1+bit/6]-63)&(1<<(5-bit%6))){a[i]|=1u<<j;a[j]|=1u<<i;}
 uint64_t checked=0,bad=0,by_size[30]={},reg_counts[30]={};uint32_t first_regular[30]={};
 auto start=std::chrono::steady_clock::now();
 for(uint32_t m=1;m<(1u<<n);m++){
  int sz=__builtin_popcount(m);if(sz<7)continue;checked++;by_size[sz]++;
  int v=__builtin_ctz(m),d=__builtin_popcount(a[v]&m);uint32_t r=m&(m-1);bool reg=true;
  while(r){int w=__builtin_ctz(r);r&=r-1;if(__builtin_popcount(a[w]&m)!=d){reg=false;break;}}
  if(reg){bad++;reg_counts[sz]++;if(!first_regular[sz])first_regular[sz]=m;}
 }
 double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
 printf("{\"vertices\":%d,\"checked_subsets\":%llu,\"regular_subsets_at_least_seven\":%llu,\"elapsed_seconds\":%.3f,\"counts_by_size\":{",n,(unsigned long long)checked,(unsigned long long)bad,elapsed);
 for(int k=7;k<=29;k++)printf("%s\"%d\":%llu",k==7?"":",",k,(unsigned long long)by_size[k]);printf("}}\n");
 return bad?1:0;
}
