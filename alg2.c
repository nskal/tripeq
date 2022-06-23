/* Stand-alone implementation of algorithm for testing linear equivalence of a 3-to-1 function to a canonical 3-to-1 function */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include "vbf.h"

bool equivalent_to_canonical = false;

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
} linear;;

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
bool is_triplicate(vbf_tt F, triplicate *T){
   
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
   if (beta==0) return false;
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
            for (k = i+1; k<F.vbf_tt_number_of_entries; k++){
               if (F.vbf_tt_values[k] == F.vbf_tt_values[i] && F.vbf_tt_values[k ^ i] == F.vbf_tt_values[i]) break;
            }
            if (k==F.vbf_tt_number_of_entries){
               fprintf (stderr, "error: Function is not triplicate. Triple not found.\n");
               return false; 
            }
         }
         T->t[2 * T->tN + j] = k;
         c[k] = 0;
         T->t[3 * T->tN + j] = k^i;
         c[k^i] = 0;
         j+=1;
      }
   }

   free(c);
   
   return true;
}

triplicate generate_empty_canonical(size_t n, vbf_tt_entry *xgs, vbf_tt_entry *cgs){
   triplicate C;
   size_t a, b;
   vbf_tt_entry i, j, k, beta;
   unsigned char *c;

   C.N = 1<<n;
   C.tN = (C.N-1)/3;
   C.t = (vbf_tt_entry *) malloc (C.tN * 4 * sizeof (vbf_tt_entry));
   memset (C.t, 0, C.tN * 4 * sizeof (vbf_tt_entry));
   C.ol = (vbf_tt_entry *) malloc (C.N * sizeof (vbf_tt_entry));
   memset (C.ol, 0, C.N * sizeof (vbf_tt_entry));

   beta = get_beta(n);
   c = (unsigned char *) malloc (C.N * sizeof (unsigned char));
   memset (c, 1, C.N * sizeof (unsigned char));

   c[0] = 0;
   j = 0;

   for(i = 1; i < C.N; i++){
      if (c[i] != 0) {
         C.t[1 * C.tN + j] = i;
         c[i] = 0;
         k = vbf_tt_ff_multiply(i, beta, vbf_tt_get_primitive_polynomial(n), n);
         C.t[2 * C.tN + j] = k;
         c[k] = 0;
         C.t[3 * C.tN + j] = k^i;
         c[k^i] = 0;
         j+=1;
      }
   }
   free(c);

   c = (unsigned char *) malloc (C.tN * sizeof (unsigned char));
   memset (c, 0, C.tN * sizeof (unsigned char));

   for (k = 0; k < n/2; k++) {
      a = (1<<(2*k))-1;
      b = a + 3;
      //find new guess
      j = 0;
      while(c[j]!=0 && j<C.tN) j+=1; 
      //guess
      cgs[k] = j;
      c[j] = 1;
      //assign
      xgs[a]   = C.t[1 * C.tN + j];
      xgs[a+1] = C.t[2 * C.tN + j];
      xgs[a+2] = C.t[3 * C.tN + j];
      //combine
      for (i = 0; i < a; i+=3){
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
      //generate
      a = (1<<(2*k))+2;
      b = (1<<(2*(k+1)))-1;
      for (i = a; i < b; i+=3){
         j = 0;
         while (C.t[C.tN+j] != xgs[i]) j+=1;
         while (j >= C.tN) j-=C.tN;
         c[j] = 1;
      }     
   }

   free(c);

   return C;

}

void retrieve_linear_and_canonical(vbf_tt T, triplicate Tt, vbf_tt_entry *ygs){
   size_t i;
   vbf_tt_entry *cgs;//c guess sequence to pick next c value (pregenerated)
   vbf_tt_entry *xgs;//x guess sequence of combined x guesses (pregenerated)

   vbf_tt C;
   triplicate Ct;
   linear L2;

   xgs = (vbf_tt_entry *) malloc (T.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
   memset (xgs, 0, T.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
   cgs = (vbf_tt_entry *) malloc ((T.vbf_tt_dimension/2) * sizeof (vbf_tt_entry));
   memset (cgs, 0, (T.vbf_tt_dimension/2) * sizeof (vbf_tt_entry));
   Ct = generate_empty_canonical(T.vbf_tt_dimension, xgs, cgs);

   C.vbf_tt_dimension = T.vbf_tt_dimension;
   C.vbf_tt_number_of_entries = T.vbf_tt_number_of_entries;
   C.vbf_tt_values = (vbf_tt_entry *) malloc (C.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
   C.vbf_tt_values[0] = 0;

   L2.x = (vbf_tt_entry *) malloc (T.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
   L2.y = (vbf_tt_entry *) malloc (T.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
   L2.N = T.vbf_tt_number_of_entries;
   L2.x[0] = 0;
   L2.y[0] = 0;

   for(i=0; i<T.vbf_tt_number_of_entries; i++){
      L2.y[xgs[i]] = ygs[i];
      L2.x[ygs[i]] = xgs[i];
      C.vbf_tt_values[xgs[i]] = T.vbf_tt_values[ygs[i]];
   }

   vbf_tt_print_truth_table(C);

   free(xgs);
   free(cgs);
   delete_triplicate_from_memory(Ct);
   delete_linear_from_memory(L2);
   vbf_tt_destroy(C);
}

void assign(vbf_tt T, triplicate Tt, size_t t, vbf_tt_entry *tgs, vbf_tt_entry *ygs, unsigned char xymc, unsigned char px);

void guess(vbf_tt T, triplicate Tt, vbf_tt_entry *tgs, vbf_tt_entry *ygs, unsigned char px){

   size_t t;

   t = 0;
   //c = cgs[px];
   
   while(tgs[t]!=0 && t<Tt.tN) t+=1;

   if (t == Tt.tN) { // || px == (T.n/2)+1) { // the second condition (||) is redundant
      retrieve_linear_and_canonical(T, Tt, ygs);
      equivalent_to_canonical = true;
      return;
   }

   //find free values to pair triples
   while (t < Tt.tN) {
      //make a guess: Ct.t[c] = Tt.t[t];
      tgs[t] = 1; //guess is made

      //and assign configuration:
      assign(T, Tt, t, tgs, ygs, 0, px);
      if (equivalent_to_canonical) return;
      
      //clear failed guess
      tgs[t] = 0;
      t+=1;
      while (tgs[t]!=0 && t<Tt.tN) t+=1;
   }
   return;

}

void combine(vbf_tt_entry *ygs, unsigned char px) {
   size_t a,b,i;

   a = (1<<(2*px))-1;
   b = a + 3;

   for (i = 0; i < a; i+=3){
      ygs[b+3*i]   = ygs[a]   ^ ygs[i];
      ygs[b+3*i+1] = ygs[a+1] ^ ygs[i+1];
      ygs[b+3*i+2] = ygs[a+2] ^ ygs[i+2];

      ygs[b+3*i+3] = ygs[a]   ^ ygs[i+1];
      ygs[b+3*i+4] = ygs[a+1] ^ ygs[i+2];
      ygs[b+3*i+5] = ygs[a+2] ^ ygs[i];

      ygs[b+3*i+6] = ygs[a]   ^ ygs[i+2];
      ygs[b+3*i+7] = ygs[a+1] ^ ygs[i];
      ygs[b+3*i+8] = ygs[a+2] ^ ygs[i+1];

   }
   
   return;

}

void configure(triplicate Ft, vbf_tt_entry *ygs, size_t f, unsigned char xymc, unsigned char px) {
   
   size_t a;
   a = (1<<(2*px))-1;

   switch (xymc)
   {
   case 0:
      ygs[a]   = Ft.t[1*Ft.tN+f];
      ygs[a+1] = Ft.t[2*Ft.tN+f];
      ygs[a+2] = Ft.t[3*Ft.tN+f];
      break;
   case 1:
      ygs[a]   = Ft.t[2*Ft.tN+f];
      ygs[a+1] = Ft.t[3*Ft.tN+f];
      ygs[a+2] = Ft.t[1*Ft.tN+f];
      break;
   case 2:
      ygs[a]   = Ft.t[3*Ft.tN+f];
      ygs[a+1] = Ft.t[1*Ft.tN+f];
      ygs[a+2] = Ft.t[2*Ft.tN+f];
      break;
   case 3:
      ygs[a]   = Ft.t[2*Ft.tN+f];
      ygs[a+1] = Ft.t[1*Ft.tN+f];
      ygs[a+2] = Ft.t[3*Ft.tN+f];
      break;
   case 4:
      ygs[a]   = Ft.t[3*Ft.tN+f];
      ygs[a+1] = Ft.t[2*Ft.tN+f];
      ygs[a+2] = Ft.t[1*Ft.tN+f];
      break;
   case 5:
      ygs[a]   = Ft.t[1*Ft.tN+f];
      ygs[a+1] = Ft.t[3*Ft.tN+f];
      ygs[a+2] = Ft.t[2*Ft.tN+f];
      break;

   default:
      return;
      break;
   }      

}

unsigned int check(vbf_tt T, triplicate Tt, vbf_tt_entry *tgs, vbf_tt_entry *ygs, unsigned char px){

   size_t a, b, i;
   vbf_tt_entry k;
   a = (1<<(2*px))+2;
   b = (1<<(2*(px+1)))-1;
   for (i = a; i < b; i+=3){
      if ((ygs[i]^ygs[i+1]^ygs[i+2])!=0) return 0; //combo not a triple
      if ((T.vbf_tt_values[ygs[i]]!=T.vbf_tt_values[ygs[i+1]])||(T.vbf_tt_values[ygs[i]]!=T.vbf_tt_values[ygs[i+2]])||(T.vbf_tt_values[ygs[i+1]]!=T.vbf_tt_values[ygs[i+2]])) return 0; //combo not a T triple
      k = Tt.ol[T.vbf_tt_values[ygs[i]]]-1;
      if(tgs[k] == 1) return 0; //combo not unique
      tgs[k] = 1;
   }
   return 1;
}

void assign(vbf_tt T, triplicate Tt, size_t t, vbf_tt_entry *tgs, vbf_tt_entry *ygs, unsigned char xymc, unsigned char px){
   
   size_t i; 
   vbf_tt_entry *tgss;

   while (xymc<6) {

      configure(Tt, ygs, t, xymc, px); //choose the assignemnt of xy map out of six possible

      //copy of tgs is required for check that will change it
      tgss = (vbf_tt_entry *) malloc (Tt.tN * sizeof (vbf_tt_entry));
      for (i = 0; i < Tt.tN; i++) tgss[i] = tgs[i];

      combine(ygs, px); //linearly combine y values to get new calculated triplets
      if (check(T, Tt, tgss, ygs, px)==1) guess(T, Tt, tgss, ygs, px+1); //check if new generated y values are unique triples and proceed to next guess
      
      free(tgss);
      if (equivalent_to_canonical) return;

      xymc+=1;

   }

   return;
}

void test_triplicate_to_canonical_triplicate_linear_equivalence (vbf_tt T, triplicate Tt) {
   size_t t;   //triple position tracker in Tt triplicate for guesses
   unsigned char xymc;//x to y map configuration for the guesses
   vbf_tt_entry *tgs;//t guess sequence to remember t guesses and check for uniquness contradiction
   vbf_tt_entry *ygs;//y guess sequence to remember y guesses (configuration) and check for triples contradiction 
   unsigned char px;  //pointer to x/y guesses

   px = 0;
   t = 0;
   xymc = 0;
   tgs = (vbf_tt_entry *) malloc (Tt.tN * sizeof (vbf_tt_entry));
   memset (tgs, 0, Tt.tN * sizeof (vbf_tt_entry));

   ygs = (vbf_tt_entry *) malloc (T.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));
   memset (ygs, 0, T.vbf_tt_number_of_entries * sizeof (vbf_tt_entry));


   //root:
   while (t < Tt.tN) {
      //make the first guess: Ct.t[c] = Tt.t[t];
      tgs[t] = 1; //guess is made

      //y sequence is generated in the config

      //and guess configuration:
      assign(T, Tt, t, tgs, ygs, xymc, px);
      if (equivalent_to_canonical) break;

      //clean up after processed guess
      tgs[t] = 0;

      //move sideways, pick another t to pair with C(0)
      t+=1;
   }

   free(tgs);
   free(ygs);

   if( ! equivalent_to_canonical) printf("False\n");

   return;
}

int main(int argc, char *argv[]){

   vbf_tt T;
   triplicate Tt;

   if(argc != 2) {
		printf("Usage: Algorithm requires 1 argument (truth table file representing a 3-to-1 function).\n");
		return 1;
	}

   T = load_vbf_tt_from_file(argv[1]);

   if( ! is_triplicate (T, &Tt)){
      vbf_tt_destroy(T);
      delete_triplicate_from_memory(Tt);
      printf("Usage: Function needs to be 3-to-1 function with zero-sum property.\n");
      return 1;
   }

   test_triplicate_to_canonical_triplicate_linear_equivalence(T, Tt);

   delete_triplicate_from_memory(Tt);
   vbf_tt_destroy(T);

   return 0;
}
