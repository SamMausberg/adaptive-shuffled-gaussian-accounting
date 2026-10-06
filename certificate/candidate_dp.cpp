// Conditional allocation stop-loss and put upper bounds.
// Compile: g++ -O2 -std=c++17 -frounding-math -ffp-contract=off
//          -fno-fast-math candidate_dp.cpp -o candidate_dp
// The proof uses only nonnegative arithmetic rounded toward +infinity.
#pragma STDC FENV_ACCESS ON
#include <algorithm>
#include <cassert>
#include <cfenv>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <sstream>
#include <string>
#include <vector>
using U=unsigned __int128;
using I=long long;
static int XB,PB;
U parse(const std::string&s){U a=0;for(char c:s){assert(c>='0'&&c<='9');a=a*10+(c-'0');}return a;}
double prob(U a){if(!a)return 0.;double d=std::nextafter(static_cast<double>(a),INFINITY);return std::ldexp(d,-PB);}
double real(I a){assert(std::abs(a)<(1LL<<53));return std::ldexp(static_cast<double>(a),-XB);}
struct Atom {I x;double p;};
struct Edge {int j;double a,b;};
struct Row {std::vector<Edge> e; double tail0=0.,tail1=0.;};
std::vector<Row> make(const std::vector<I>&grid,const std::vector<Atom>&law,bool call){
 std::vector<Row> rows(grid.size());
 for(size_t i=0;i<grid.size();++i){
  auto&r=rows[i];r.e.reserve(law.size());
  for(const auto&v:law){
   I q=grid[i]-v.x;
   if(q<0){if(call){r.tail0+=v.p*real(-q);r.tail1+=v.p;}continue;}
   auto it=std::upper_bound(grid.begin(),grid.end(),q);
   int j=std::min<int>(grid.size()-2,it-grid.begin()-1);
   assert(j>=0 && grid[j]<=q && q<=grid[j+1]);
   const double denom=static_cast<double>(grid[j+1]-grid[j]);
   const double a=v.p*(static_cast<double>(grid[j+1]-q)/denom);
   const double b=v.p*(static_cast<double>(q-grid[j])/denom);
   r.e.push_back({j,a,b});
  }
 }
 return rows;
}
double at(const std::vector<I>&grid,const std::vector<double>&f,I q,bool call){
 if(q==grid.back())return f.back();
 if(q>grid.back()){assert(call);return 0.;}
 assert(q>=0);
 auto it=std::upper_bound(grid.begin(),grid.end(),q);int j=it-grid.begin()-1;
 assert(j>=0 && j+1<(int)grid.size());
 double denom=static_cast<double>(grid[j+1]-grid[j]);
 double a=static_cast<double>(grid[j+1]-q)/denom;
 double b=static_cast<double>(q-grid[j])/denom;
 return a*f[j]+b*f[j+1];
}
int main(int argc,char**argv){
 static_assert(std::numeric_limits<double>::is_iec559,"IEEE binary64 required");
 assert(argc==3);assert(std::fesetround(FE_UPWARD)==0);assert(std::fegetround()==FE_UPWARD);
 volatile double one=1.,small=std::ldexp(1.,-54);volatile double bumped=one+small;assert(bumped>1.);
 std::ifstream in(argv[1]);assert(in.good());
 int M,nf,nr,af,ar;in>>M>>XB>>PB>>nf>>nr>>af>>ar;
 std::vector<I>gf(nf),gr(nr);for(auto&x:gf)in>>x;for(auto&x:gr)in>>x;
 auto readlaw=[&](int n){std::vector<Atom>a;U sum=0;for(int i=0;i<n;i++){I x;std::string w;in>>x>>w;U v=parse(w);sum+=v;a.push_back({x,prob(v)});}assert(sum==(U(1)<<PB));return a;};
 auto lf=readlaw(af),lr=readlaw(ar);
 double mean=0;for(auto a:lf)mean+=a.p*real(a.x);
 std::vector<std::vector<I>>tf(556,std::vector<I>(M)),tr=tf;
 for(int j=0;j<556;j++)for(int m=0;m<M;m++)in>>tf[j][m]>>tr[j][m];assert(in.good());
 std::cerr<<"Preparing upward transitions: "<<nf<<"+"<<nr<<" nodes.\n";
 auto rf=make(gf,lf,true);auto rr=make(gr,lr,false);
 std::vector<double>f(nf,0),p(nr);for(int i=0;i<nr;i++)p[i]=real(gr[i]);
 std::ofstream out(argv[2]);out<<"# conditional call and put upper endpoints; binary64 hex; FE_UPWARD\n";
 out<<M<<" "<<556<<"\n";
 for(int m=1;m<=M;m++){
  std::vector<double>fn(nf),pn(nr);
  for(int i=0;i<nf;i++){
   const auto&r=rf[i];double v=r.tail0+static_cast<double>(m-1)*mean*r.tail1;
   for(auto e:r.e)v+=e.a*f[e.j]+e.b*f[e.j+1];
   assert(v>=0&&std::isfinite(v));fn[i]=v;
  }
  for(int i=0;i<nr;i++){
   double v=0;for(auto e:rr[i].e)v+=e.a*p[e.j]+e.b*p[e.j+1];
   assert(v>=0&&std::isfinite(v));pn[i]=v;
  }
  f.swap(fn);p.swap(pn);
  for(int j=0;j<556;j++){
   out<<m<<" "<<j<<" "<<std::hexfloat<<at(gf,f,tf[j][m-1],true)<<" "<<at(gr,p,tr[j][m-1],false)<<"\n";
  }
  if(m%8==0)std::cerr<<"candidate count "<<m<<" of "<<M<<" complete\n";
 }
 assert(std::fegetround()==FE_UPWARD);return 0;
}
