/* Stand-alone implementation of algorithm for generating the self-equivalence classes */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include "vbf.h"

// Object: Triplicate Boolean function truth table
typedef struct triplicates {
   size_t N;      //number of elements
   size_t tN;     //number of triples 
   vbf_tt_entry *t;     //triplicate table / output & 3 preimages
   vbf_tt_entry *ol;    //output lookup
} triplicate;

typedef struct linears {
   size_t N;      //number of elements
   vbf_tt_entry *y;     // x -> y values
   vbf_tt_entry *x;    // y -> x pre-images
} linear;

void delete_triplicate_from_memory(triplicate T){
   free(T.t);
   free(T.ol);
   return;
}

void delete_linear_from_memory(linear L){
   free(L.y);
   free(L.x);
   return;
}

void print_linear(linear L){
   size_t i;

   printf("\n");
   for (i = 0; i < L.N; i++){    
      printf("%lu ",L.y[i]);
   }
   printf("\n");
//   for (i = 0; i < L.N; i++){    
//      printf("%u ",L.x[i]);
//   }
//   printf("\n");

   return;
}

//pre-generated betas for the triplicate functions from dimension 4 to dimension 20
vbf_tt_entry get_beta (size_t n) {
   if (n < 4 || n > 20 || n % 2) {
      fprintf (stderr, "error: Beta is a primitive element of F2^4 in even dimension n: 4 <= n <= 20.\n");
      return 0;
   }
   vbf_tt_entry beta[] = {6, 14, 214, 42, 3363, 16363, 44234, 245434, 476308};
   return beta[(n-4)/2];
}

//Function: check if triplicate and return triplicate representation
bool is_canonical_triplicate(vbf_tt F, triplicate *T){
   vbf_tt_entry i, j, k;
   vbf_tt_entry beta;
   unsigned char *c;

   if (F.vbf_tt_dimension < 4 || F.vbf_tt_dimension > 20 || F.vbf_tt_dimension % 2) {
      fprintf (stderr, "error: Triplicate functions exist in even dimensions n >=4. Max n=20 implemented.\n");
      return false;
   }

   if (F.vbf_tt_values[0]!=0){
      fprintf (stderr, "error: Function is not triplicate. F(0) =/= 0.\n");
      return false;
   }

   T->N = F.vbf_tt_number_of_entries;
   T->tN = (F.vbf_tt_number_of_entries-1)/3;
   T->t = (vbf_tt_entry *) malloc (T->tN * 4 * sizeof (vbf_tt_entry));
   memset (T->t, 0, T->tN * 4 * sizeof (vbf_tt_entry));
   T->ol = (vbf_tt_entry *) malloc (T->N * sizeof (vbf_tt_entry));
   memset (T->ol, 0, T->N * sizeof (vbf_tt_entry));

   beta = get_beta(F.vbf_tt_dimension);
   c = (unsigned char *) malloc (T->N * sizeof (unsigned char));
   memset (c, 1, T->N * sizeof (unsigned char));

   c[0] = 0;
   j = 0;

   for(i = 1; i < F.vbf_tt_number_of_entries; i++){
      if (c[i] != 0) {
         if (F.vbf_tt_values[i] == 0) {
            fprintf (stderr, "error: Function is not canonical triplicate. Too many elements map to 0.\n");
            return false;
         }
         if(T->ol[F.vbf_tt_values[i]] != 0) {
            fprintf (stderr, "error: Function is not canonical triplicate. Too many elements map to same value.\n");
            return false;
         }
         T->ol[F.vbf_tt_values[i]] = j + 1;
         T->t[0 * T->tN + j] = F.vbf_tt_values[i];
         T->t[1 * T->tN + j] = i;
         c[i] = 0;
         k = vbf_tt_ff_multiply(i, beta, vbf_tt_get_primitive_polynomial(F.vbf_tt_dimension), F.vbf_tt_dimension);
         if (F.vbf_tt_values[k] != F.vbf_tt_values[i] || F.vbf_tt_values[k ^ i] != F.vbf_tt_values[i]) {
            fprintf (stderr, "error: Function is not canonical triplicate. Triple not found.\n");
            return false;
         }
         T->t[2 * T->tN + j] = k;
         c[k] = 0;
         T->t[3 * T->tN + j] = k^i;
         c[k^i] = 0;
         j+=1;
      }
   }

   free(c);
   
/*    printf("\n");
   for (j = 0; j < 4; j++){
      for (i = 0; i < T.tN; i++) printf("%u ",T.t[j*T.tN+i]);
      printf("\n");
   }   
   printf("\n");
 */
   return true;
}

void assign(vbf_tt F, vbf_tt G, triplicate Ft, triplicate Gt, linear L1, linear L2, size_t f, size_t g, vbf_tt_entry *fgs, vbf_tt_entry *xgs, 
            unsigned char xymc, unsigned char px, unsigned char cfg);

bool check(vbf_tt F, vbf_tt G, triplicate Ft, triplicate Gt, linear L1, vbf_tt_entry *fgs, size_t a) {
   
   size_t b, i, j, k, n;
   vbf_tt_entry f, g;
   b = 0;
   while(fgs[b]!=0) b++;
   n = b;
   k = b;

   for(i = a; i < b; i++){
      for(j = 0; j < i; j++){
         f = fgs[i]^fgs[j];
         g = L1.y[fgs[i]]^L1.y[fgs[j]];
         if ((f==0 && g!=0)||(g==0 && f!=0)) return false;
         if (L1.x[g]!=0 && L1.x[g]!=f) return false;
         if (L1.y[f]!=0 && L1.y[f]!=g) return false;
         if (L1.y[f]==0 && f!=0){
            if(Ft.ol[f]!=0 && Gt.ol[g]!=0){ //if both values are present as triplet outputs
               fgs[k] = f;
               k += 1;
               L1.y[f] = g;
               L1.x[g] = f;

            } else if (Ft.ol[f]==0 && Gt.ol[g]==0) { //if both values are not present in triplet outputs
               fgs[k] = f;
               fgs[F.vbf_tt_number_of_entries+k] = 1; // we will not derive any info from there, therefore it is ok to set them to assigned
               k += 1;
               L1.y[f] = g;
               L1.x[g] = f;

            } else return false;  // contradiction
         }
      }
      for(j = b; j < n; j++){
         f = fgs[i]^fgs[j];
         g = L1.y[fgs[i]]^L1.y[fgs[j]];
         if ((f==0 && g!=0)||(g==0 && f!=0)) return false;
         if (L1.x[g]!=0 && L1.x[g]!=f) return false;
         if (L1.y[f]!=0 && L1.y[f]!=g) return false;
         if (L1.y[f]==0 && f!=0){
            if(Ft.ol[f]!=0 && Gt.ol[g]!=0){
               fgs[k] = f;
               k += 1;
               L1.y[f] = g;
               L1.x[g] = f;

            } else if (Ft.ol[f]==0 && Gt.ol[g]==0) {
               fgs[k] = f;
               fgs[F.vbf_tt_number_of_entries+k] = 1;
               k += 1;
               L1.y[f] = g;
               L1.x[g] = f;

            } else return false;  
         }
      }
      n = k;
   }

   return true;

}

void guess(vbf_tt F, vbf_tt G, triplicate Ft, triplicate Gt, linear L1, linear L2, vbf_tt_entry *fgs, vbf_tt_entry *xgs, unsigned char px, unsigned char cfg){

   size_t i, pf, n;
   vbf_tt_entry f, g, *fgss;
   linear l1,l2;

   l1.N = L1.N;
   l2.N = L2.N;
   n = (1<<(2*px)) - 1;

   for (i = 0; i<F.vbf_tt_number_of_entries-1; i++){
      if (fgs[F.vbf_tt_number_of_entries+i]==0) {
         pf = i;
         break;
      }
   }
   if (i == F.vbf_tt_number_of_entries-1) {// || px == (F.vbf_tt_dimension/2)+1) { // one of these conditions is enough
      print_linear(L1);
      print_linear(L2);
      return;
   }

   if (fgs[pf]!=0){

      f = Ft.ol[fgs[pf]]-1;
      g = Gt.ol[L1.y[fgs[pf]]]-1;

      l2.x = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
      l2.y = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
      fgss = (vbf_tt_entry *) malloc (2*F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));

      for (i = 0; i < F.vbf_tt_number_of_entries; i++) {
         l2.x[i] = L2.x[i];
         l2.y[i] = L2.y[i];
         fgss[i] = fgs[i];
         fgss[F.vbf_tt_number_of_entries + i] = fgs[F.vbf_tt_number_of_entries + i];
      }
      //add its L2 values to L2 guesses
      fgss[F.vbf_tt_number_of_entries + pf] = 1; //mark the guess as configured
      xgs[n]  =Gt.t[1*Gt.tN+g];
      xgs[n+1]=Gt.t[2*Gt.tN+g];
      xgs[n+2]=Gt.t[3*Gt.tN+g];

      //and assign L2 configuration:
      assign(F, G, Ft, Gt, L1, l2, f, g, fgss, xgs, 0, px, cfg);
      delete_linear_from_memory(l2);
      free(fgss);

   } else {
      //find free values to pair for L1
      f = 0;
      g = 0;
      while (L1.y[Ft.t[f]]!=0 && f < Ft.tN) f += 1;
      while (L1.x[Gt.t[g]]!=0 && g < Gt.tN) g += 1;
      while (g < Gt.tN) {
         //generate a copy of L1 and fgs not to mess 'em up
         l1.x = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
         l1.y = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
         fgss = (vbf_tt_entry *) malloc (2*F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));

         for (i = 0; i < F.vbf_tt_number_of_entries; i++) {
            l1.x[i] = L1.x[i];
            l1.y[i] = L1.y[i];
            fgss[i] = fgs[i];
            fgss[F.vbf_tt_number_of_entries + i] = fgs[F.vbf_tt_number_of_entries + i];
         }

         //make a guess; give new assignment to L1
         l1.y[Ft.t[f]] = Gt.t[g];
         l1.x[Gt.t[g]] = Ft.t[f];
         fgss[pf] = Ft.t[f];

         //generate its linear combos and check
         if(check(F, G, Ft, Gt, l1, fgss, pf)==1) {

            fgss[F.vbf_tt_number_of_entries + pf] = 1; //mark the guess as configured
            l2.x = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
            l2.y = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
            for (i = 0; i < F.vbf_tt_number_of_entries; i++) {
               l2.x[i] = L2.x[i];
               l2.y[i] = L2.y[i];
            }
            //add its L2 values to L2 guesses
            xgs[n]=Gt.t[1*Gt.tN+g];
            xgs[n+1]=Gt.t[2*Gt.tN+g];
            xgs[n+2]=Gt.t[3*Gt.tN+g];

            //and assign L2 configuration:
            assign(F, G, Ft, Gt, l1, l2, f, g, fgss, xgs, 0, px, cfg);
            delete_linear_from_memory(l2);
         }

         delete_linear_from_memory(l1);
         free(fgss);
         g+=1;
         while (L1.x[Gt.t[g]]!=0 && g < Gt.tN) g+=1;
      }
   }
   return;

}

void combine(linear L2, vbf_tt_entry *xgs, unsigned char px) {
   size_t a,b,i;

   a = (1<<(2*px))-1;
   b = a + 3;

   for (i = 0; i < a; i+=3){
      //come up with linear combos and add them to Linears and guesses
      L2.y[xgs[a]^xgs[i]] = L2.y[xgs[a]] ^ L2.y[xgs[i]];
      L2.y[xgs[a+1]^xgs[i+1]] = L2.y[xgs[a+1]] ^ L2.y[xgs[i+1]];
      L2.y[xgs[a+2]^xgs[i+2]] = L2.y[xgs[a+2]] ^ L2.y[xgs[i+2]];
      L2.x[L2.y[xgs[a]^xgs[i]]] = xgs[a] ^ xgs[i];
      L2.x[L2.y[xgs[a+1]^xgs[i+1]]] = xgs[a+1] ^ xgs[i+1];
      L2.x[L2.y[xgs[a+2]^xgs[i+2]]] = xgs[a+2] ^ xgs[i+2];

      L2.y[xgs[a]^xgs[i+1]] = L2.y[xgs[a]] ^ L2.y[xgs[i+1]];
      L2.y[xgs[a+1]^xgs[i+2]] = L2.y[xgs[a+1]] ^ L2.y[xgs[i+2]];
      L2.y[xgs[a+2]^xgs[i]] = L2.y[xgs[a+2]] ^ L2.y[xgs[i]];
      L2.x[L2.y[xgs[a]^xgs[i+1]]] = xgs[a] ^ xgs[i+1];
      L2.x[L2.y[xgs[a+1]^xgs[i+2]]] = xgs[a+1] ^ xgs[i+2];
      L2.x[L2.y[xgs[a+2]^xgs[i]]] = xgs[a+2] ^ xgs[i];

      L2.y[xgs[a]^xgs[i+2]] = L2.y[xgs[a]] ^ L2.y[xgs[i+2]];
      L2.y[xgs[a+1]^xgs[i]] = L2.y[xgs[a+1]] ^ L2.y[xgs[i]];
      L2.y[xgs[a+2]^xgs[i+1]] = L2.y[xgs[a+2]] ^ L2.y[xgs[i+1]];
      L2.x[L2.y[xgs[a]^xgs[i+2]]] = xgs[a] ^ xgs[i+2];
      L2.x[L2.y[xgs[a+1]^xgs[i]]] = xgs[a+1] ^ xgs[i];
      L2.x[L2.y[xgs[a+2]^xgs[i+1]]] = xgs[a+2] ^ xgs[i+1];

      //last but not least, add them to guess list as well
      xgs[b+3*i]   = xgs[a]   ^ xgs[i];
      xgs[b+3*i+1] = xgs[a+1] ^ xgs[i+1];
      xgs[b+3*i+2] = xgs[a+2] ^ xgs[i+2];

      xgs[b+3*i+3] = xgs[a]   ^ xgs[i+1];
      xgs[b+3*i+4] = xgs[a+1] ^ xgs[i+2];
      xgs[b+3*i+5] = xgs[a+2] ^ xgs[i];

      xgs[b+3*i+6] = xgs[a]   ^ xgs[i+2];
      xgs[b+3*i+7] = xgs[a+1] ^ xgs[i];
      xgs[b+3*i+8] = xgs[a+2] ^ xgs[i+1];

   }
   
   return;

}

void configure(triplicate Ft, triplicate Gt, linear L2, size_t f, size_t g, unsigned char xymc, unsigned char cfg) {

   if (cfg==1){
      switch (xymc)
      {
      case 0:
         L2.y[Gt.t[1*Gt.tN+g]] = Ft.t[1*Ft.tN+f];
         L2.x[Ft.t[1*Ft.tN+f]] = Gt.t[1*Gt.tN+g];
         L2.y[Gt.t[2*Gt.tN+g]] = Ft.t[2*Ft.tN+f];
         L2.x[Ft.t[2*Ft.tN+f]] = Gt.t[2*Gt.tN+g];
         L2.y[Gt.t[3*Gt.tN+g]] = Ft.t[3*Ft.tN+f];
         L2.x[Ft.t[3*Ft.tN+f]] = Gt.t[3*Gt.tN+g];
         break;
      case 1:
         L2.y[Gt.t[1*Gt.tN+g]] = Ft.t[2*Ft.tN+f];
         L2.x[Ft.t[2*Ft.tN+f]] = Gt.t[1*Gt.tN+g];
         L2.y[Gt.t[2*Gt.tN+g]] = Ft.t[3*Ft.tN+f];
         L2.x[Ft.t[3*Ft.tN+f]] = Gt.t[2*Gt.tN+g];
         L2.y[Gt.t[3*Gt.tN+g]] = Ft.t[1*Ft.tN+f];
         L2.x[Ft.t[1*Ft.tN+f]] = Gt.t[3*Gt.tN+g];
         break;
      case 2:
         L2.y[Gt.t[1*Gt.tN+g]] = Ft.t[3*Ft.tN+f];
         L2.x[Ft.t[3*Ft.tN+f]] = Gt.t[1*Gt.tN+g];
         L2.y[Gt.t[2*Gt.tN+g]] = Ft.t[1*Ft.tN+f];
         L2.x[Ft.t[1*Ft.tN+f]] = Gt.t[2*Gt.tN+g];
         L2.y[Gt.t[3*Gt.tN+g]] = Ft.t[2*Ft.tN+f];
         L2.x[Ft.t[2*Ft.tN+f]] = Gt.t[3*Gt.tN+g];
         break;

      default:
         return;
         break;
      }
   } else {
      switch (xymc)
      {
      case 0:
         L2.y[Gt.t[1*Gt.tN+g]] = Ft.t[2*Ft.tN+f];
         L2.x[Ft.t[2*Ft.tN+f]] = Gt.t[1*Gt.tN+g];
         L2.y[Gt.t[2*Gt.tN+g]] = Ft.t[1*Ft.tN+f];
         L2.x[Ft.t[1*Ft.tN+f]] = Gt.t[2*Gt.tN+g];
         L2.y[Gt.t[3*Gt.tN+g]] = Ft.t[3*Ft.tN+f];
         L2.x[Ft.t[3*Ft.tN+f]] = Gt.t[3*Gt.tN+g];
         break;
      case 1:
         L2.y[Gt.t[1*Gt.tN+g]] = Ft.t[3*Ft.tN+f];
         L2.x[Ft.t[3*Ft.tN+f]] = Gt.t[1*Gt.tN+g];
         L2.y[Gt.t[2*Gt.tN+g]] = Ft.t[2*Ft.tN+f];
         L2.x[Ft.t[2*Ft.tN+f]] = Gt.t[2*Gt.tN+g];
         L2.y[Gt.t[3*Gt.tN+g]] = Ft.t[1*Ft.tN+f];
         L2.x[Ft.t[1*Ft.tN+f]] = Gt.t[3*Gt.tN+g];
         break;
      case 2:
         L2.y[Gt.t[1*Gt.tN+g]] = Ft.t[1*Ft.tN+f];
         L2.x[Ft.t[1*Ft.tN+f]] = Gt.t[1*Gt.tN+g];
         L2.y[Gt.t[2*Gt.tN+g]] = Ft.t[3*Ft.tN+f];
         L2.x[Ft.t[3*Ft.tN+f]] = Gt.t[2*Gt.tN+g];
         L2.y[Gt.t[3*Gt.tN+g]] = Ft.t[2*Ft.tN+f];
         L2.x[Ft.t[2*Ft.tN+f]] = Gt.t[3*Gt.tN+g];
         break;

      default:
         return;
         break;
      }      
   }

}

size_t generate(vbf_tt F, vbf_tt G, linear L1, linear L2, vbf_tt_entry *fgs, vbf_tt_entry *xgs, unsigned char px){

   size_t a, b, i, j, k, n;
   vbf_tt_entry f, g;

   a = (1<<(2*px))+2;
   b = (1<<(2*(px+1)))-1;
   n = 0;
   while(fgs[n]!=0) n++;
   j = n; // j is a position indicator to return, start of newly added values (the ones that have not been linearly combined yet)

   for (i = a; i < b; i+=3){
      g = G.vbf_tt_values[xgs[i]];
      f = F.vbf_tt_values[L2.y[xgs[i]]];
      if ((f==0 && g!=0)||(g==0 && f!=0)) return 0; // redundant condition
      if (L1.x[g]!=0 && L1.x[g]!=f) return 0;
      if (L1.y[f]!=0 && L1.y[f]!=g) return 0;
      if (L1.y[f]!=0){
         for (k = 0; k < n; k++) { 
            if(fgs[k]==f){
               fgs[F.vbf_tt_number_of_entries+k] = 1;
               break;
            }
         }
      } else {
         fgs[n] = f;
         fgs[F.vbf_tt_number_of_entries+n] = 1;
         n += 1;
         L1.y[f] = g;
         L1.x[g] = f;
      }
   }
   
   return j;

}

void assign(vbf_tt F, vbf_tt G, triplicate Ft, triplicate Gt, linear L1, linear L2, size_t f, size_t g, vbf_tt_entry *fgs, vbf_tt_entry *xgs, 
            unsigned char xymc, unsigned char px, unsigned char cfg){
   
   size_t i, a; 
   vbf_tt_entry *fgss;
   linear l1,l2;

   while (xymc<3) {

      configure(Ft, Gt, L2, f, g, xymc, cfg); //choose the assignemnt of xy map out of three possible

      //give a copy of L2 to the functions that will change it
      l1.x = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
      l1.y = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
      l1.N = F.vbf_tt_number_of_entries;
      l2.x = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
      l2.y = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
      l2.N = F.vbf_tt_number_of_entries;
      
      //copy of f guesses since we need those clean every time to know how many new asssignments has been made
      fgss = (vbf_tt_entry *) malloc (2*F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));

      for (i = 0; i < F.vbf_tt_number_of_entries; i++) {
         l1.x[i] = L1.x[i];
         l1.y[i] = L1.y[i];
         l2.x[i] = L2.x[i];
         l2.y[i] = L2.y[i];
         fgss[i] = fgs[i];
         fgss[F.vbf_tt_number_of_entries + i] = fgs[F.vbf_tt_number_of_entries + i];
      }      

      combine(l2, xgs, px); //linearly combine L2 values to get new calculated triplets
      a = generate(F, G, l1, l2, fgss, xgs, px); //generate L1 values from new L2 triplets
      if (a!=0){
         if(check(F, G, Ft, Gt, l1, fgss, a)) { //linearly combine new values in L1 and check for contradiction
            guess(F, G, Ft, Gt, l1, l2, fgss, xgs, px+1, cfg); // if all is good, proceed to the next unasigned guess of L1
         }
      }

      delete_linear_from_memory(l1);
      delete_linear_from_memory(l2);
      free(fgss);

      xymc+=1;

   }

   return;
}

void test_triplicate_linear_equivalence (vbf_tt F, vbf_tt G, triplicate Ft, triplicate Gt) {
   size_t f;   //position tracker in Ft triplicate for L1 guesses
   size_t g;   //position tracker in Gt triplicate for L1 guesses L1(Ft(f)) = Gt(g)
   vbf_tt_entry *fgs;//f guess sequence to remember f guesses and speed up linear combos
   vbf_tt_entry *xgs;//x guess sequence to remember x guesses and speed up linear combos
   unsigned char xymc;//x to y map configuration for the L2 guesses
   unsigned char px;  //pointer to x guesses

   linear L1, L2;

   L1.N = F.vbf_tt_number_of_entries;
   L2.N = F.vbf_tt_number_of_entries;

   L1.x = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
   L1.y = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
   memset (L1.x, 0, F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
   memset (L1.y, 0, F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
   L2.x = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
   L2.y = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));

   f = 0;
   g = 0;
   px = 0;
   xymc = 0;
   fgs = (vbf_tt_entry *) malloc (2*F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
   memset (fgs, 0, 2*F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));

   xgs = (vbf_tt_entry *) malloc (F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
   memset (xgs, 0, F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));


   //root:
   while (g < Gt.tN) {
      //make the first guess for L1:
      L1.y[Ft.t[f]] = Gt.t[g];
      L1.x[Gt.t[g]] = Ft.t[f];
      //remember the guess in sequences:
      fgs[0] = Ft.t[f];
      fgs[F.vbf_tt_number_of_entries] = 1; //mark the guess 0 as configured (L2 derived)
      xgs[0] = Gt.t[1*Gt.tN+g];
      xgs[1] = Gt.t[2*Gt.tN+g];
      xgs[2] = Gt.t[3*Gt.tN+g];
      //clean L2 for use:
      memset (L2.x, 0, F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
      memset (L2.y, 0, F.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
      //and guess L2 configuration:
      assign(F, G, Ft, Gt, L1, L2, f, g, fgs, xgs, xymc, px, 1); //first configuration set
      assign(F, G, Ft, Gt, L1, L2, f, g, fgs, xgs, xymc, px, 2); //second configuration set
      //clean up after processed guess
      L1.y[Ft.t[f]] = 0;
      L1.x[Gt.t[g]] = 0;
      //move sideways, pick another g to pair with L1(F(1))
      g+=1;
   }

   delete_linear_from_memory(L1);
   delete_linear_from_memory(L2);
   
   return;
}

int main(int argc, char *argv[]){

   vbf_tt F, G;
   triplicate Ft, Gt;

   if(argc != 2) {
		printf("Usage: Algorithm requires 1 argument (truth table file representing canonical 3-to-1 function).\n");
		return 1;
	}

   F = load_vbf_tt_from_file(argv[1]);
   G = load_vbf_tt_from_file(argv[1]);

   if( ! is_canonical_triplicate (F, &Ft) || ! is_canonical_triplicate (G, &Gt)){
      vbf_tt_destroy(F);
      vbf_tt_destroy(G);
      delete_triplicate_from_memory(Ft);
      delete_triplicate_from_memory(Gt);
      printf("Usage: Functions needs to be canonical 3-to-1 function.\n");
      return 1;
   }

   test_triplicate_linear_equivalence(F, G, Ft, Gt);

   delete_triplicate_from_memory(Ft);
   delete_triplicate_from_memory(Gt);
   vbf_tt_destroy(F);
   vbf_tt_destroy(G);

   return 0;
}
