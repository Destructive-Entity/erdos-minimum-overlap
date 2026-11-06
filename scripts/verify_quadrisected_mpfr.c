/*
 * Independent direct-MPFR verifier for the frozen weighted spectral-Parseval
 * center certificate supporting c_E > 0.38056070.
 *
 * Trusted path: exact terminating-decimal certificate data; MPFR directed
 * rounding; sixth-order Taylor sign enclosure with a global seventh-derivative
 * remainder; exact elementary antiderivative on sign-positive cells; and
 * conservative width*upper(q) charging on terminal ambiguous cells.
 *
 * No mpmath, NumPy, SciPy, Arb, root finder, LP solver, or archived numerical
 * upper bound is used.  The caller supplies decimal-grid endpoints in units of
 * 1/10000; recursive bisection is exact on the resulting rational grid.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#ifdef MPFR_SELFDECL
typedef unsigned long mp_limb_t; typedef long mpfr_prec_t; typedef int mpfr_sign_t; typedef long mpfr_exp_t; typedef int mpfr_rnd_t;
typedef struct { mpfr_prec_t _mpfr_prec; mpfr_sign_t _mpfr_sign; mpfr_exp_t _mpfr_exp; mp_limb_t *_mpfr_d; } __mpfr_struct;
typedef __mpfr_struct mpfr_t[1]; typedef __mpfr_struct *mpfr_ptr; typedef const __mpfr_struct *mpfr_srcptr;
enum { MPFR_RNDN=0, MPFR_RNDZ=1, MPFR_RNDU=2, MPFR_RNDD=3, MPFR_RNDA=4 };
extern void mpfr_init2(mpfr_ptr,mpfr_prec_t); extern void mpfr_clear(mpfr_ptr); extern int mpfr_set(mpfr_ptr,mpfr_srcptr,mpfr_rnd_t); extern int mpfr_set_str(mpfr_ptr,const char*,int,mpfr_rnd_t); extern int mpfr_set_si(mpfr_ptr,long,mpfr_rnd_t); extern int mpfr_set_ui(mpfr_ptr,unsigned long,mpfr_rnd_t); extern int mpfr_add(mpfr_ptr,mpfr_srcptr,mpfr_srcptr,mpfr_rnd_t); extern int mpfr_sub(mpfr_ptr,mpfr_srcptr,mpfr_srcptr,mpfr_rnd_t); extern int mpfr_mul(mpfr_ptr,mpfr_srcptr,mpfr_srcptr,mpfr_rnd_t); extern int mpfr_div(mpfr_ptr,mpfr_srcptr,mpfr_srcptr,mpfr_rnd_t); extern int mpfr_div_ui(mpfr_ptr,mpfr_srcptr,unsigned long,mpfr_rnd_t); extern int mpfr_div_2ui(mpfr_ptr,mpfr_srcptr,unsigned long,mpfr_rnd_t); extern int mpfr_mul_ui(mpfr_ptr,mpfr_srcptr,unsigned long,mpfr_rnd_t); extern int mpfr_neg(mpfr_ptr,mpfr_srcptr,mpfr_rnd_t); extern int mpfr_sin(mpfr_ptr,mpfr_srcptr,mpfr_rnd_t); extern int mpfr_sin_cos(mpfr_ptr,mpfr_ptr,mpfr_srcptr,mpfr_rnd_t); extern int mpfr_const_pi(mpfr_ptr,mpfr_rnd_t); extern int mpfr_cmp(mpfr_srcptr,mpfr_srcptr); extern int mpfr_cmp_si(mpfr_srcptr,long); extern double mpfr_get_d(mpfr_srcptr,mpfr_rnd_t); extern char *mpfr_get_str(char*,mpfr_exp_t*,int,size_t,mpfr_srcptr,mpfr_rnd_t); extern void mpfr_free_str(char*);
#else
#include <mpfr.h>
#endif
#ifndef PREC
#define PREC 192
#endif
#ifndef MEAN_DENOM
#define MEAN_DENOM 1280
#endif
#if MEAN_DENOM <= 0 || MEAN_DENOM > 1000000
#error "MEAN_DENOM must be in 1..1000000"
#endif
#define SCALE 10000ULL
#define NCOS 80
#define NPI 400
#define ORDER 6

typedef struct{mpfr_t lo,hi;} iv;
typedef struct{iv w,c,anti;} term_t;
typedef struct{uint64_t a,b;unsigned d;} cell_t;
static mpfr_t S[32]; static int SR=0; static iv QCONST,QB2,PIIV; static mpfr_t M7UP; static term_t TERMS[NCOS+NPI]; static int NT=0;
static char T2_LAM[128], WIN_LAM[128];
static char COS_XI[NCOS][128], COS_LAM[NCOS][128];
static char PI_COEF[NPI][128];
static const unsigned long FACT[8]={1,1,2,6,24,120,720,5040};
static void sinit(void){if(SR)return;for(int i=0;i<32;i++)mpfr_init2(S[i],PREC);SR=1;} static void sclear(void){if(!SR)return;for(int i=0;i<32;i++)mpfr_clear(S[i]);SR=0;}
static void ii(iv*a){mpfr_init2(a->lo,PREC);mpfr_init2(a->hi,PREC);}static void ic(iv*a){mpfr_clear(a->lo);mpfr_clear(a->hi);}static void iset(iv*r,const iv*a){mpfr_set(r->lo,a->lo,MPFR_RNDN);mpfr_set(r->hi,a->hi,MPFR_RNDN);}static void isi(iv*r,long x){mpfr_set_si(r->lo,x,MPFR_RNDN);mpfr_set_si(r->hi,x,MPFR_RNDN);}static void iui(iv*r,unsigned long x){mpfr_set_ui(r->lo,x,MPFR_RNDN);mpfr_set_ui(r->hi,x,MPFR_RNDN);}static void idec(iv*r,const char*s){if(mpfr_set_str(r->lo,s,10,MPFR_RNDD)||mpfr_set_str(r->hi,s,10,MPFR_RNDU)){fprintf(stderr,"bad decimal %s\n",s);exit(2);}}static void iratio(iv*r,unsigned long p,unsigned long q){mpfr_set_ui(r->lo,p,MPFR_RNDN);mpfr_set_ui(r->hi,p,MPFR_RNDN);mpfr_div_ui(r->lo,r->lo,q,MPFR_RNDD);mpfr_div_ui(r->hi,r->hi,q,MPFR_RNDU);}
static void ineg(iv*r,const iv*a){mpfr_neg(S[0],a->hi,MPFR_RNDD);mpfr_neg(S[1],a->lo,MPFR_RNDU);mpfr_set(r->lo,S[0],MPFR_RNDN);mpfr_set(r->hi,S[1],MPFR_RNDN);}static void iadd(iv*r,const iv*a,const iv*b){mpfr_add(S[0],a->lo,b->lo,MPFR_RNDD);mpfr_add(S[1],a->hi,b->hi,MPFR_RNDU);mpfr_set(r->lo,S[0],MPFR_RNDN);mpfr_set(r->hi,S[1],MPFR_RNDN);}static void isub(iv*r,const iv*a,const iv*b){mpfr_sub(S[0],a->lo,b->hi,MPFR_RNDD);mpfr_sub(S[1],a->hi,b->lo,MPFR_RNDU);mpfr_set(r->lo,S[0],MPFR_RNDN);mpfr_set(r->hi,S[1],MPFR_RNDN);}static void imul(iv*r,const iv*a,const iv*b){mpfr_mul(S[0],a->lo,b->lo,MPFR_RNDD);mpfr_mul(S[1],a->lo,b->hi,MPFR_RNDD);mpfr_mul(S[2],a->hi,b->lo,MPFR_RNDD);mpfr_mul(S[3],a->hi,b->hi,MPFR_RNDD);mpfr_set(S[8],S[0],MPFR_RNDN);for(int i=1;i<4;i++)if(mpfr_cmp(S[i],S[8])<0)mpfr_set(S[8],S[i],MPFR_RNDN);mpfr_mul(S[4],a->lo,b->lo,MPFR_RNDU);mpfr_mul(S[5],a->lo,b->hi,MPFR_RNDU);mpfr_mul(S[6],a->hi,b->lo,MPFR_RNDU);mpfr_mul(S[7],a->hi,b->hi,MPFR_RNDU);mpfr_set(S[9],S[4],MPFR_RNDN);for(int i=5;i<8;i++)if(mpfr_cmp(S[i],S[9])>0)mpfr_set(S[9],S[i],MPFR_RNDN);mpfr_set(r->lo,S[8],MPFR_RNDN);mpfr_set(r->hi,S[9],MPFR_RNDN);}static void isq(iv*r,const iv*a){if(mpfr_cmp_si(a->lo,0)>=0){mpfr_mul(r->lo,a->lo,a->lo,MPFR_RNDD);mpfr_mul(r->hi,a->hi,a->hi,MPFR_RNDU);return;}if(mpfr_cmp_si(a->hi,0)<=0){mpfr_mul(r->lo,a->hi,a->hi,MPFR_RNDD);mpfr_mul(r->hi,a->lo,a->lo,MPFR_RNDU);return;}mpfr_set_si(r->lo,0,MPFR_RNDN);mpfr_mul(S[0],a->lo,a->lo,MPFR_RNDU);mpfr_mul(S[1],a->hi,a->hi,MPFR_RNDU);mpfr_set(r->hi,mpfr_cmp(S[0],S[1])>0?S[0]:S[1],MPFR_RNDN);}static void idivpos(iv*r,const iv*a,const iv*b){if(mpfr_cmp_si(b->lo,0)<=0){fprintf(stderr,"division by nonpositive interval\n");exit(2);}iv z;ii(&z);mpfr_set_ui(z.lo,1,MPFR_RNDN);mpfr_set_ui(z.hi,1,MPFR_RNDN);mpfr_div(z.lo,z.lo,b->hi,MPFR_RNDD);mpfr_div(z.hi,z.hi,b->lo,MPFR_RNDU);imul(r,a,&z);ic(&z);}static void absup(mpfr_ptr r,const iv*a){if(mpfr_cmp_si(a->lo,0)>=0){mpfr_set(r,a->hi,MPFR_RNDU);return;}if(mpfr_cmp_si(a->hi,0)<=0){mpfr_neg(r,a->lo,MPFR_RNDU);return;}mpfr_neg(S[0],a->lo,MPFR_RNDU);mpfr_set(r,mpfr_cmp(S[0],a->hi)>0?S[0]:a->hi,MPFR_RNDU);}static void widthup(mpfr_ptr r,const iv*a){mpfr_sub(r,a->hi,a->lo,MPFR_RNDU);}
static void sincosiv(iv*s,iv*c,const iv*z){mpfr_sin_cos(S[0],S[1],z->lo,MPFR_RNDD);mpfr_sin_cos(S[2],S[3],z->lo,MPFR_RNDU);widthup(S[4],z);mpfr_sub(s->lo,S[0],S[4],MPFR_RNDD);mpfr_add(s->hi,S[2],S[4],MPFR_RNDU);mpfr_sub(c->lo,S[1],S[4],MPFR_RNDD);mpfr_add(c->hi,S[3],S[4],MPFR_RNDU);if(mpfr_cmp_si(s->lo,-1)<0)mpfr_set_si(s->lo,-1,MPFR_RNDN);if(mpfr_cmp_si(s->hi,1)>0)mpfr_set_si(s->hi,1,MPFR_RNDN);if(mpfr_cmp_si(c->lo,-1)<0)mpfr_set_si(c->lo,-1,MPFR_RNDN);if(mpfr_cmp_si(c->hi,1)>0)mpfr_set_si(c->hi,1,MPFR_RNDN);}static void siniv(iv*s,const iv*z){mpfr_sin(S[0],z->lo,MPFR_RNDD);mpfr_sin(S[1],z->lo,MPFR_RNDU);widthup(S[2],z);mpfr_sub(s->lo,S[0],S[2],MPFR_RNDD);mpfr_add(s->hi,S[1],S[2],MPFR_RNDU);if(mpfr_cmp_si(s->lo,-1)<0)mpfr_set_si(s->lo,-1,MPFR_RNDN);if(mpfr_cmp_si(s->hi,1)>0)mpfr_set_si(s->hi,1,MPFR_RNDN);}
static void iscaled(iv*r,uint64_t num,unsigned d){mpfr_set_ui(r->lo,(unsigned long)num,MPFR_RNDN);mpfr_set_ui(r->hi,(unsigned long)num,MPFR_RNDN);mpfr_div_ui(r->lo,r->lo,SCALE,MPFR_RNDD);mpfr_div_ui(r->hi,r->hi,SCALE,MPFR_RNDU);mpfr_div_2ui(r->lo,r->lo,d,MPFR_RNDD);mpfr_div_2ui(r->hi,r->hi,d,MPFR_RNDU);}static void pprint(const char*l,mpfr_srcptr x){mpfr_exp_t e;char*s=mpfr_get_str(NULL,&e,10,75,x,MPFR_RNDU);if(!s)exit(2);int neg=s[0]=='-';char*d=s+neg;printf("%s%s",l,neg?"-":"");long n=strlen(d);if(e<=0){printf("0.");for(long k=0;k<-e;k++)putchar('0');printf("%s",d);}else if(e>=n){printf("%s",d);for(long k=n;k<e;k++)putchar('0');}else{fwrite(d,1,e,stdout);putchar('.');printf("%s",d+e);}putchar('\n');mpfr_free_str(s);}
static void addterm(const iv*w,const iv*c){term_t*t=&TERMS[NT++];ii(&t->w);ii(&t->c);ii(&t->anti);iset(&t->w,w);iset(&t->c,c);idivpos(&t->anti,c,w);}
static void load_coeffs(const char*path){
    FILE*f=fopen(path,"r"); if(!f){perror(path);exit(2);} char tag[32],a[128],b[128]; int n,cosn=0,pin=0;
    if(fscanf(f,"%31s %127s",tag,a)!=2||strcmp(tag,"FORMAT")||strcmp(a,"weighted-center-coefficients-v1")){fprintf(stderr,"bad coefficient format\n");exit(2);}
    while(fscanf(f,"%31s",tag)==1){
        if(!strcmp(tag,"T2")){ if(fscanf(f,"%127s",T2_LAM)!=1)exit(2); }
        else if(!strcmp(tag,"WINDOW")){ if(fscanf(f,"%127s",WIN_LAM)!=1)exit(2); }
        else if(!strcmp(tag,"COS")){ if(cosn>=NCOS||fscanf(f,"%127s %127s",COS_XI[cosn],COS_LAM[cosn])!=2)exit(2); cosn++; }
        else if(!strcmp(tag,"PI")){ if(fscanf(f,"%d %127s",&n,b)!=2||n<1||n>NPI)exit(2); strncpy(PI_COEF[n-1],b,127); PI_COEF[n-1][127]=0; pin++; }
        else { fprintf(stderr,"unknown coefficient tag %s\n",tag); exit(2); }
    }
    fclose(f); if(cosn!=NCOS||pin!=NPI||!T2_LAM[0]||!WIN_LAM[0]){fprintf(stderr,"coefficient count mismatch cos=%d pi=%d\n",cosn,pin);exit(2);}
}
static void prep(const char*coeffpath){
    load_coeffs(coeffpath); sinit();ii(&QCONST);ii(&QB2);ii(&PIIV);mpfr_init2(M7UP,PREC);isi(&QCONST,1);isi(&QB2,0);mpfr_const_pi(PIIV.lo,MPFR_RNDD);mpfr_const_pi(PIIV.hi,MPFR_RNDU);mpfr_set_si(M7UP,0,MPFR_RNDN);
    iv lam,tmp,B,s,c,sinc,w,coef,niv;ii(&lam);ii(&tmp);ii(&B);ii(&s);ii(&c);ii(&sinc);ii(&w);ii(&coef);ii(&niv);
    idec(&lam,T2_LAM);iratio(&B,2,3);iratio(&tmp,1,2UL*MEAN_DENOM*MEAN_DENOM);iadd(&B,&B,&tmp);mpfr_set(B.lo,B.hi,MPFR_RNDN);imul(&tmp,&lam,&B);iadd(&QCONST,&QCONST,&tmp);isub(&QB2,&QB2,&lam);
    for(int j=0;j<NCOS;j++){idec(&w,COS_XI[j]);idec(&lam,COS_LAM[j]);sincosiv(&s,&c,&w);idivpos(&sinc,&s,&w);isq(&B,&sinc);mpfr_set(B.lo,B.hi,MPFR_RNDN);imul(&tmp,&lam,&B);iadd(&QCONST,&QCONST,&tmp);ineg(&coef,&lam);addterm(&w,&coef);}
    idec(&lam,WIN_LAM);iratio(&B,1,2);imul(&tmp,&lam,&B);iadd(&QCONST,&QCONST,&tmp);
    for(int n=1;n<=NPI;n++){idec(&coef,PI_COEF[n-1]);if(mpfr_cmp_si(coef.lo,0)==0&&mpfr_cmp_si(coef.hi,0)==0)continue;iui(&niv,n);imul(&w,&PIIV,&niv);addterm(&w,&coef);}
    for(int j=0;j<NT;j++){absup(S[0],&TERMS[j].c);absup(S[1],&TERMS[j].w);mpfr_set_ui(S[2],1,MPFR_RNDN);for(int k=0;k<7;k++)mpfr_mul(S[2],S[2],S[1],MPFR_RNDU);mpfr_mul(S[3],S[0],S[2],MPFR_RNDU);mpfr_add(M7UP,M7UP,S[3],MPFR_RNDU);}
    ic(&lam);ic(&tmp);ic(&B);ic(&s);ic(&c);ic(&sinc);ic(&w);ic(&coef);ic(&niv);
}
static void cleanup(void){for(int j=0;j<NT;j++){ic(&TERMS[j].w);ic(&TERMS[j].c);ic(&TERMS[j].anti);}ic(&QCONST);ic(&QB2);ic(&PIIV);mpfr_clear(M7UP);sclear();}
static void derivs(iv*d,const iv*x){for(int j=0;j<=ORDER;j++)isi(&d[j],0);iv x2,z,s,c,wp,tmp,base;ii(&x2);ii(&z);ii(&s);ii(&c);ii(&wp);ii(&tmp);ii(&base);isq(&x2,x);imul(&tmp,&QB2,&x2);iadd(&d[0],&QCONST,&tmp);imul(&tmp,&QB2,x);iadd(&d[1],&tmp,&tmp);iadd(&d[2],&QB2,&QB2);for(int k=0;k<NT;k++){imul(&z,&TERMS[k].w,x);sincosiv(&s,&c,&z);isi(&wp,1);for(int j=0;j<=ORDER;j++){if(j)imul(&wp,&wp,&TERMS[k].w);switch(j&3){case 0:iset(&base,&c);break;case 1:ineg(&base,&s);break;case 2:ineg(&base,&c);break;default:iset(&base,&s);}imul(&tmp,&TERMS[k].c,&wp);imul(&tmp,&tmp,&base);iadd(&d[j],&d[j],&tmp);}}ic(&x2);ic(&z);ic(&s);ic(&c);ic(&wp);ic(&tmp);ic(&base);}
static void Qeval(iv*out,const iv*x){iv x2,x3,z,s,tmp;ii(&x2);ii(&x3);ii(&z);ii(&s);ii(&tmp);imul(out,&QCONST,x);isq(&x2,x);imul(&x3,&x2,x);imul(&tmp,&QB2,&x3);mpfr_div_ui(tmp.lo,tmp.lo,3,MPFR_RNDD);mpfr_div_ui(tmp.hi,tmp.hi,3,MPFR_RNDU);iadd(out,out,&tmp);for(int k=0;k<NT;k++){imul(&z,&TERMS[k].w,x);siniv(&s,&z);imul(&tmp,&TERMS[k].anti,&s);iadd(out,out,&tmp);}ic(&x2);ic(&x3);ic(&z);ic(&s);ic(&tmp);}
int main(int ac,char**av){if(ac<4){fprintf(stderr,"usage: %s COEFF_FILE LO_UNITS_1E4 HI_UNITS_1E4 [MAX_DEPTH]\n",av[0]);return 2;}const char*coeffpath=av[1];uint64_t A=strtoull(av[2],0,10),B=strtoull(av[3],0,10);int maxd=ac>4?atoi(av[4]):20;if(!(A<B)||B>20000){fprintf(stderr,"bad range\n");return 2;}prep(coeffpath);size_t cap=1<<18,sp=1;cell_t*st=malloc(cap*sizeof(cell_t));st[0]=(cell_t){A,B,0};mpfr_t D,r,rad,rp,hi,lo,con;mpfr_init2(D,PREC);mpfr_init2(r,PREC);mpfr_init2(rad,PREC);mpfr_init2(rp,PREC);mpfr_init2(hi,PREC);mpfr_init2(lo,PREC);mpfr_init2(con,PREC);mpfr_set_si(D,0,MPFR_RNDN);iv x,ds[ORDER+1],Qa,Qb;ii(&x);ii(&Qa);ii(&Qb);for(int j=0;j<=ORDER;j++)ii(&ds[j]);long nodes=0,pos=0,neg=0,amb=0;while(sp){cell_t z=st[--sp];nodes++;uint64_t mid=z.a+z.b;unsigned md=z.d+1;iscaled(&x,mid,md);derivs(ds,&x);mpfr_set_ui(r,(unsigned long)(z.b-z.a),MPFR_RNDN);mpfr_div_ui(r,r,SCALE,MPFR_RNDU);mpfr_div_2ui(r,r,md,MPFR_RNDU);mpfr_set_si(rad,0,MPFR_RNDN);mpfr_set_ui(rp,1,MPFR_RNDN);for(int j=1;j<=ORDER;j++){mpfr_mul(rp,rp,r,MPFR_RNDU);absup(S[0],&ds[j]);mpfr_mul(S[1],S[0],rp,MPFR_RNDU);mpfr_div_ui(S[1],S[1],FACT[j],MPFR_RNDU);mpfr_add(rad,rad,S[1],MPFR_RNDU);}mpfr_mul(rp,rp,r,MPFR_RNDU);mpfr_mul(S[1],M7UP,rp,MPFR_RNDU);mpfr_div_ui(S[1],S[1],FACT[7],MPFR_RNDU);mpfr_add(rad,rad,S[1],MPFR_RNDU);mpfr_sub(lo,ds[0].lo,rad,MPFR_RNDD);mpfr_add(hi,ds[0].hi,rad,MPFR_RNDU);if(mpfr_cmp_si(hi,0)<=0){neg++;continue;}if(mpfr_cmp_si(lo,0)>0){iscaled(&x,z.a,z.d);Qeval(&Qa,&x);iscaled(&x,z.b,z.d);Qeval(&Qb,&x);mpfr_sub(con,Qb.hi,Qa.lo,MPFR_RNDU);if(mpfr_cmp_si(con,0)<0){fprintf(stderr,"negative integral\n");return 2;}mpfr_add(D,D,con,MPFR_RNDU);pos++;continue;}/* exact width <=1/20000 iff 2*(b-a)<=2^d */int terminal=(z.d<63 && 2*(z.b-z.a)<=((uint64_t)1<<z.d));if(terminal||((int)z.d>=maxd)){mpfr_set_ui(S[0],(unsigned long)(z.b-z.a),MPFR_RNDN);mpfr_div_ui(S[0],S[0],SCALE,MPFR_RNDU);mpfr_div_2ui(S[0],S[0],z.d,MPFR_RNDU);mpfr_mul(con,S[0],hi,MPFR_RNDU);if(mpfr_cmp_si(con,0)>0)mpfr_add(D,D,con,MPFR_RNDU);amb++;continue;}if(sp+2>=cap){cap*=2;st=realloc(st,cap*sizeof(cell_t));if(!st)return 2;}st[sp++]=(cell_t){mid,2*z.b,md};st[sp++]=(cell_t){2*z.a,mid,md};}printf("MPFR6 weighted quadrisected center verifier\nrange_units_1e4: [%llu,%llu]\nnodes: %ld\npositive_cells: %ld\nnegative_cells: %ld\nambiguous_terminal_cells: %ld\n",(unsigned long long)A,(unsigned long long)B,nodes,pos,neg,amb);pprint("Dhalf_upper: ",D);printf("CHUNK_CERTIFIED True\n");free(st);for(int j=0;j<=ORDER;j++)ic(&ds[j]);ic(&x);ic(&Qa);ic(&Qb);mpfr_clear(D);mpfr_clear(r);mpfr_clear(rad);mpfr_clear(rp);mpfr_clear(hi);mpfr_clear(lo);mpfr_clear(con);cleanup();return 0;}
