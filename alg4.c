/* Clean stand-alone implementation of the triplicate equivalence algorithm */
/* In this version, we assume that the triplicate function has the triple summation property */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "vbf.h"

/* Parameters */
_Bool output_all = false; /* whether we stop at the first equivalent triplicate, or output all of them */

/* Global structures for the search */
size_t N; /* number of elements in finite field */
size_t TARGET_IMAGE_SIZE; /* number of images, including 0 */
vbf_tt * T; /* partial TT of the triplicate function */
vbf_tt * F; /* TT of the input function */
size_t * ASSIGNMENTS; /* linearly independent set of elements whose values we know */
size_t K; /* size of the above array */
_Bool * PREDICTED_IMAGE_SET_MAP;

_Bool result_found = false; /* we will set this to "true" in output_truth_table() */

/* Linked lists */
typedef struct linked_list_node ll;
struct linked_list_node {
  void * data;
  struct linked_list_node * ll_prev;
  struct linked_list_node * ll_next;
};

ll * ll_initialize_empty_linked_list(void) {
  ll * l = malloc(sizeof(ll));
  l->data = 0;
  l->ll_prev = l;
  l->ll_next = l;
  return l;
}

/* Bit mask for the last n = dimension(F) elements */
size_t m = 0;

/* Inserts element at the first position, e,g. for START -> A -> B -> C, we would get START -> X -> A -> B -> C after inserting X */
void ll_push(ll * l, void * data) {
  ll * new_node = malloc(sizeof(ll));
  new_node->data = data;
  new_node->ll_prev = l;
  new_node->ll_next = l->ll_next;
  l->ll_next->ll_prev = new_node;
  l->ll_next = new_node;
}

/* Returns the first element from the linked list (see the ll_push() method above) and removes it from the list */
void * ll_pop(ll * l) {
  if(l->ll_next == l) {
    return 0;
  }

  ll * target_node = l->ll_next;
  target_node->ll_prev->ll_next = target_node->ll_next;
  target_node->ll_next->ll_prev = target_node->ll_prev;
  void * data = target_node->data;
  free(target_node);
  return data;
}

void ll_copy_linked_list(ll * target, ll * src) {
  ll * l = src->ll_next;
  while(l != src) {
    ll_push(target, l->data);
    l = l->ll_next;
  }
}

/* Destroys only the structures allocated for the linked list; FREEING THE ACTUAL DATA IS NOT MY RESPONSIBILITY!!! */
void ll_destroy(ll * l) {
  ll * target_node = l->ll_next;
  while(target_node != l) {
    target_node = target_node->ll_next;
    free(target_node->ll_prev);
  }
  free(l);
}


/* Structures for the list of compatible pairs and preimage lists */

_Bool ** compatible_pair_maps;
size_t ** pre_image_lists; 
ll * processed_triples;


ll * T_stack; /* stack of truth tables of T from recursive calls */
ll * preimage_stack; /* same for pre_image_lists */
ll * triples_stack; /* list (of linked lists) of known (and already processed triples) */

void initialize_structures(void) {
  T = malloc(sizeof(vbf_tt));
  T->vbf_tt_dimension = F->vbf_tt_dimension;
  T->vbf_tt_number_of_entries = N;
  T->vbf_tt_values = calloc( sizeof(size_t), N );

  ASSIGNMENTS = calloc(sizeof(size_t), T->vbf_tt_dimension);

  PREDICTED_IMAGE_SET_MAP = calloc(sizeof(_Bool), N);

  pre_image_lists = malloc(sizeof(size_t *) * N);
  for(size_t y = 1; y < N; ++y) {
    pre_image_lists[y] = calloc( sizeof(size_t), 3 );
  }

  compatible_pair_maps = malloc(sizeof(_Bool *) * N);
  for(size_t x = 1; x < N; ++x) {
    compatible_pair_maps[x] = calloc( sizeof(_Bool), N );
  }

  processed_triples = ll_initialize_empty_linked_list();

  T_stack = ll_initialize_empty_linked_list();
  preimage_stack = ll_initialize_empty_linked_list();
  triples_stack = ll_initialize_empty_linked_list();

  m = 1;
  for(size_t j = 1; j < F->vbf_tt_dimension; ++j) {
    m <<= 1;
    m |= 1;
  }
}

void push_structures(void) {
  /* We need to backup the following structures:
   * - partial truth table for T;
   * - preimage lists
   */

  size_t * backup_tt = malloc(sizeof(size_t) * N);
  memcpy(backup_tt, T->vbf_tt_values, sizeof(size_t) * N);
  ll_push(T_stack, backup_tt);

  size_t ** backup_preimages = malloc(sizeof(size_t *) * N);
  for(size_t y = 1; y < N; ++y) {
    backup_preimages[y] = malloc(sizeof(size_t) * 3);
    memcpy(backup_preimages[y], pre_image_lists[y], sizeof(size_t) * 3);
  }
  ll_push(preimage_stack, backup_preimages);

  ll * new_ll = ll_initialize_empty_linked_list();
  ll_copy_linked_list(new_ll, processed_triples);
  ll_push(triples_stack, new_ll);
}

void pop_structures(void) {
  size_t * backup_tt = (size_t *) ll_pop(T_stack);
  memcpy(T->vbf_tt_values, backup_tt, sizeof(size_t) * N);
  free(backup_tt);

  size_t ** backup_preimages = (size_t **) ll_pop(preimage_stack);
  for(size_t y = 1; y < N; ++y) {
    memcpy(pre_image_lists[y], backup_preimages[y], sizeof(size_t) * 3);
    free(backup_preimages[y]);
  }
  free(backup_preimages);

  ll_destroy(processed_triples);
  processed_triples = ll_pop(triples_stack);
}

void destroy_structures(void) {
  free(T->vbf_tt_values);
  free(T);

  free(ASSIGNMENTS);

  free(PREDICTED_IMAGE_SET_MAP);

  for(size_t y = 1; y < N; ++y) {
    free(pre_image_lists[y]);
  }
  free(pre_image_lists);

  for(size_t x = 1; x < N; ++x) {
    free(compatible_pair_maps[x]);
  }
  free(compatible_pair_maps);

  ll_destroy(processed_triples);

  ll_destroy(T_stack);
  ll_destroy(preimage_stack);
  ll_destroy(triples_stack);
}

/* Adds a new compatible pair to the registry */
void add_compatible_pair(size_t x, size_t y) {
  compatible_pair_maps[x][y] = true;
  compatible_pair_maps[y][x] = true;
}

/* Checks whether a pair (x,y) is compatible, i.e. whether x and y can belong to the same triple */
_Bool is_pair_compatible(size_t x, size_t y) {
  return compatible_pair_maps[x][y];
}

size_t pack_triple(size_t x, size_t y, size_t z) {
  size_t a;

  /* Using a as an auxiliary variable, "manually" sort [x,y,z] in ascending order */
  if( x > y ) {
    a = y;
    y = x;
    x = a;
  }

  if ( y > z ) {
    a = z;
    z = y;
    y = a;
  }

  if( x > y ) {
    a = y;
    y = x;
    x = a;
  }

  size_t t = (x << F->vbf_tt_dimension) | y;

  return t;
}

/* Adds a triple to the processed_triples linked list */
void register_triple(size_t x, size_t y, size_t z) {
  /* The triples is represented as a pair of elements encoded in a single word. We take the smallest
   * two elements {a,b} among {x,y,z} such that a < b, and put them in the same size_t
   * using bit shifts.
   */
  size_t t = pack_triple(x,y,z);

  ll_push(processed_triples, (void *) t);
}

_Bool verify_summation_property(size_t a, size_t b, size_t c, size_t x, size_t y, size_t z) {
  size_t * V = T->vbf_tt_values; /* for sheer convenience */

  _Bool success = false;
  /* Verify that a^x forms a triple with some other combination */
  //if( V[a^x] == V[b^y] && V[a^x] == V[c^z] ) {
  //  success = true;
  //} else if( V[a^x] == V[b^z] && V[a^x] == V[c^y] ) {
  //  success = true;
  //}
  //if(!success) return false;

  /* Ditto for a^y */
  //if( V[a^y] == V[b^x] && V[a^y] == V[c^z] ) {
  //  success = true;
  //} else if( V[a^y] == V[b^z] && V[a^y] == V[c^x] ) {
  //  success = true;
  //}
  //if(!success) return false;

  return true;
}

/* Adds x as a preimage of y. Returns false upon any violation encountered */
_Bool add_preimage(size_t x, size_t y) {
  size_t * preimages = pre_image_lists[y];
  
  /* If x already is a preimage of y, there is nothing to do */
  if(preimages[0] == x || preimages[1] == x || preimages[2] == x) {
    return true;
  }

  /* If we already have 3 preimages, something is wrong */
  if(preimages[2]) {
    return false;
  }

  /* If we have 2 preimages, and x is not their sum, something is wrong */
  if(preimages[1] && (preimages[0] ^ preimages[1]) != x) {
    return false;
  }

  /* Otherwise, we insert x in the first empty position */
  if(!preimages[0]) {
    preimages[0] = x;
    return true;
  }

  if(!preimages[1]) {
    preimages[1] = x;
    return true;
  }

  /* Note that in this case, we have just completed a triple that was not known before. We
   * thus verify the triple summation proeperty for all other known triples and, if all is
   * okay, add this new triple to the linked list of known triples.
   */

  preimages[2] = x;
  register_triple(preimages[0], preimages[1], preimages[2]);
  return true;
}

/* Returns the number of known pre-images of a given element */
size_t number_of_preimages(size_t y) {
  size_t * preimages = pre_image_lists[y];
  if(!preimages[0]) return 0;
  if(!preimages[1]) return 1;
  if(!preimages[2]) return 2;
  return 3;
}

void dbg_print_preimages(void) {
  for(size_t y = 1; y < N; ++y) {
    printf("%lu (%lu): ", y, number_of_preimages(y));
    size_t j = 0;
    while( j < 3 && pre_image_lists[y][j] ) {
      printf("%lu ", pre_image_lists[y][j]);
      ++j;
    }
    printf("\n");
  }
}


/* Derives all possible values of T that can be obtained from a new assignment T[x] = v. Returns true
 * iff no violations are encountered.
 */
_Bool assign_new_value(size_t x, size_t v, size_t y, size_t z) {
  /* We go through the linear span of the previously assigned elements, derive all new possible values,
   * and add them to the truth table
   */


  /* Note that the number of elements in ASSIGNMENTS is K. */
  for(size_t linear_combination = 1; linear_combination < (1L << K); ++linear_combination) {
    size_t old_x = 0;
    for(size_t j = 0; j < K; ++j) {
      if( (1L << j) & linear_combination) {
	old_x ^= ASSIGNMENTS[j];
      }
    }

    /* We can now derive the value of new_x = x ^ old_x */
    size_t new_x = x ^ old_x;
    size_t new_value = T->vbf_tt_values[old_x] ^ v ^ F->vbf_tt_values[old_x] ^ F->vbf_tt_values[x] ^ F->vbf_tt_values[new_x];

    /* If this value is outside the predicted image set, we can backtrack immediately */
    if(!PREDICTED_IMAGE_SET_MAP[new_value]) {
      //printf("%lu %lu %lu\n", x, old_x, new_x);
      //printf("Image not in predicted image set: %lu->%lu\n", new_x,new_value);
      return false;
    }

    /* If for some ungodly reason this contradicts a previous derivation, we can backtrack right here and now */
    if(T->vbf_tt_values[new_x] && T->vbf_tt_values[new_x] != new_value) {
      //printf("The impossible has happened, all is lost...\n");
      return false;
    }

    /* Otherwise, we update the truth table and add a new preimage */
    T->vbf_tt_values[new_x] = new_value;
    if(!add_preimage(new_x, new_value)) {
      return false;
    }
  }


  return true;
}

/* Checks the preimages for violations (this should be called after assign_new_value() */
_Bool check_for_violations(size_t x, size_t v, size_t y, size_t z) {
  /* Here we basically verify that no preimage violates any conditions; namely, the size of 
   * a preimage should never be equal to exactly 2.
   * Note that the condition of all 3 elements adding up to zero, and there being no more
   * than 3 elements in a preimage, should have been already enforced by add_preimage().
   * If we are at this point, this is the only possible violation that remains.
   */

  ll * triples = ll_initialize_empty_linked_list();

  for(size_t y = 1; y < N; ++y) {
    if(number_of_preimages(y) == 2) {

      if(T->vbf_tt_values[1] == 1 && K == 2 && v == 8) {
	printf("We are here ma %lu %lu\n", y, v);
	printf("Known inputs: \n");
	for(size_t i = 0; i < N; ++i) {
	  if(T->vbf_tt_values[i]) {
	    printf("%lu ", i);
	  }
	}
	printf("\n");
	dbg_print_preimages();
      }
      return false;
    }

    if(number_of_preimages(y) == 3) {
      ll * l = triples->ll_next;
      size_t a = pre_image_lists[y][0];
      size_t b = pre_image_lists[y][1];
      size_t c = pre_image_lists[y][2];
      while(l != triples) {
	size_t t = (size_t) l->data;
	size_t y = t & m;
	size_t x = t >> F->vbf_tt_dimension;
	size_t z = x^y;
	if(!verify_summation_property(a,b,c,x,y,z)) {
	  printf("Verifying something or other\n");
	  return false;
	}
	l = l->ll_next;
      }
      size_t t = pack_triple(a,b,c);
      ll_push(triples, (void *) t);
    }
  }

  ll_destroy(triples);

  /* TODO This would be the place to add the "triple + triple = triple" condition for the
   * canonical equivalence test.
   */

  return true;
}

void output_truth_table(void) {
  for(size_t x = 0; x < N; ++x) {
    printf("%lu ", T->vbf_tt_values[x]);
  }
  printf("\n");
  result_found = true;
}


void guess_triple() {
  //if(K) {
  //  printf("Entering with K at %lu\n", K);
  //  ll * l = processed_triples->ll_next;
  //  while(l != processed_triples) {
  //    size_t t = (size_t) l->data;
  //    size_t m = 1;
  //    for(size_t j = 1; j < F->vbf_tt_dimension; ++j) {
  //      m <<= 1;
  //      m |= 1;
  //    }
  //    size_t y = t & m;
  //    size_t x = t >> F->vbf_tt_dimension;
  //    printf("(%lu,%lu,%lu) ", x,y,x^y);
  //    l = l->ll_next;
  //  }
  //  printf("\n");

  //  //for(size_t j = 0; j < K; ++j) {
  //  //  printf("%lu ", ASSIGNMENTS[j]);
  //  //}
  //  //printf("\n");
  //  vbf_tt_print_truth_table(*T);
  //}

  /* Find the first element in the TT whose value we do not know */
  size_t new_x = 1;
  while(new_x < N && T->vbf_tt_values[new_x]) {
    ++new_x;
  }

  /* If all elements are already known, then we have reached the end of the search, and simply need to output
   * the table
   */
  if(new_x >= N) {
    output_truth_table();
    return;
  }

  /* Otherwise, we have found an element new_x whose value under T we do not know yet. In particular, we do not know
   * which triple it belongs to. We now try to guess another element from the triple. To cut symmetries, we only
   * consider elements new_y such that new_y < new_x ^ new_y.
   */
  for(size_t new_y = 1; new_y < N; ++new_y) {
    if(new_y > (new_x ^ new_y)) {
      continue;
    }

    /* We check that (new_x, new_y) is a compatible pair */
    if(!is_pair_compatible(new_x, new_y)) {
      continue;
    }

    /* We also check that new_y has not already been assigned to a triple */
    if(T->vbf_tt_values[new_y] && number_of_preimages(T->vbf_tt_values[new_y]) > 1) {
      continue;
    }

    /* We derive the value of T[new_x] */
    size_t new_z = new_x ^ new_y;
    size_t new_value = F->vbf_tt_values[new_x] ^ F->vbf_tt_values[new_y] ^ F->vbf_tt_values[new_z];
    //if(new_x == 1) {
    //  printf("AS 1 -> %lu\n", new_value);
    //}

    /* If we already know T[new_y], it should match this value */
    if(T->vbf_tt_values[new_y] && T->vbf_tt_values[new_y] != new_value) {
      continue;
    }

    /* Same for new_z */
    if(T->vbf_tt_values[new_z] && T->vbf_tt_values[new_z] != new_value) {
      continue;
    }

    /* Otherwise, we can try to assign T[new_x] = T[new_y] = T[new_z] = new_value. This will
     * result in the structures being updated with new derivations, which may lead to
     * contradictions and backtracking, so we backup the current state of the structures first.
     */

    push_structures();

    //if(K) {
    //  printf("Attempting to assign %lu %lu %lu -> %lu at K=%lu\n", new_x, new_y, new_z, new_value, K);
    //}

    /* We first set T[new_x] = new_value, and derive all that we possibly can. It is possible that
     * we will immediately get a contradiction. We only proceed further if we do not.
     */

    _Bool all_good = true;

    size_t K_delta = 0; /* whether we should increase the value of K by 1 or 2 in the recursive call, i.e. whether
			   new_x and new_y are linearly independent or not */

    /* If new_y can be expressed as a linear combination of new_x and some known element, then we must know that
     * element, so it's value will be non-zero in the partial truth table.
     */
    if(T->vbf_tt_values[new_x ^ new_y]) {
      K_delta = 1;
    } else {
      K_delta = 2;
    }

    T->vbf_tt_values[new_x] = new_value;
    T->vbf_tt_values[new_y] = new_value;
    T->vbf_tt_values[new_z] = new_value;
    all_good = add_preimage(new_x, new_value) && add_preimage(new_y, new_value) && add_preimage(new_z, new_value);

    //printf("Before assignment:\n");
    //vbf_tt_print_truth_table(*T);

    if(all_good) {
      all_good = assign_new_value(new_x, new_value, new_y, new_z);
    }

    /* If everything has gone well, we check the resulting set for preimage violations. */

    ASSIGNMENTS[K] = new_x;

    /* If everything is still okay, we can try to derive additional things from the value of new_y and new_z,
     * provided those haven't already been set.
     */
    if(all_good && K_delta == 2) {
      ++K;
      all_good = assign_new_value(new_y, new_value, new_x, new_z);
      --K;

      ASSIGNMENTS[K+1] = new_y;
    }

    if(all_good) {
      if(!T->vbf_tt_values[new_z]) {
	++K;
	all_good = assign_new_value(new_z, new_value, new_x, new_y);
	--K;
      }

      /* Note that we do not increment ASSIGNMENTS, since new_z is always
       * dependent on new_x and new_y.
       */
    }

      if(all_good) {

	all_good = check_for_violations(new_z, new_value, new_x, new_y);
      }


    /* If we have survived all the way up to this point, then no violations have
     * been encountered whatsoever, and we can proceed to the next guess.
     */

    if(all_good) {
      K += K_delta;
      guess_triple();
      K -= K_delta;
    }

    /* At this point, we proceed to guessing a different value of new_y, so we restore the auxiliary
     * structures back to their previous state.
     */
    pop_structures();

    /* If a result has been found, and we are only looking for one result (as opposed to all possible
     * results), we can immediately return.
     */
    if(result_found && !output_all) {
      return;
    }

    ASSIGNMENTS[K+1] = ASSIGNMENTS[K] = 0;
  }
}

void is_equivalent_to_triplicate(vbf_tt f) {
  /* First, we compute the multiplicities of all elements in the multiset {* F(x) + F(y) + F(x+y) *}; the should
   * split the field into images and non-images
   */
  size_t N = (1L << f.vbf_tt_dimension);
  size_t multiplicities [N];
  for(size_t i = 0; i < N; ++i) {
    multiplicities[i] = 0;
  }

  for(size_t x = 1; x < N; ++x) {
    for(size_t y = 1; y < N; ++y) {
      if(x != y) { /* so that we only look at actual linear flat (note that flats can repeat, and that is okay */
	++multiplicities[ f.vbf_tt_values[x] ^ f.vbf_tt_values[y] ^ f.vbf_tt_values[x^y] ];
      }
    }
  }

  /* If the function is equivalent to a triplicate, we should have exactly two multiplicities; we first find out what they are */
  size_t multiplicity_a = multiplicities[1];
  size_t i = 1;
  for( ; multiplicities[i] == multiplicity_a && i < N; ++i);
  /* If we only have one multiplicity somehow, the function is not triplicate-equivalent */
  if(i >= N) {
    return;
  }
  size_t multiplicity_b = multiplicities[i];
  /* Check the remaining multiplicities to make sure that we do not have more */
  for( ; i < N; ++i) {
    if(multiplicities[i] != multiplicity_a && multiplicities[i] != multiplicity_b) {
      //printf("%lu %lu vs %lu at %lu\n", multiplicity_a, multiplicity_b, multiplicities[i], i);
      return;
    }
  }

  /* If everything is fine, then we count how many times we have each multiplicity */
  size_t count_a = 0;
  size_t count_b = 0;

  for(size_t i = 1; i < N; ++i) {
    if(multiplicities[i] == multiplicity_a) {
      ++count_a;
    } else {
      ++count_b;
    }
  }

  /* One of the two counts should be exactly twice as large as the other one; we want the one
   * having fewer instances to be multiplicity_a
   */
  if (count_a > count_b) {
    size_t tmp = count_a;
    count_a = count_b;
    count_b = tmp;

    tmp = multiplicity_a;
    multiplicity_a = multiplicity_b;
    multiplicity_b = tmp;
  }

  if(2*count_a != count_b) {
    return;
  }

  initialize_structures();

  /* If everything is alright, then the elements with multiplicity_a should correspond to the image.
   * The simplest solution right now is to make a Boolean map giving this image */
  for(size_t i = 1; i < N; ++i) {
    if(multiplicities[i] == multiplicity_a) {
      PREDICTED_IMAGE_SET_MAP[i] = true;
    }
  }

  /* At this point, we can obtain a list of admissible pairs, i.e. pairs (a,b) that we know
   * can belong to the same triplication triple. We put these in a hash table so we can
   * pull them out later. For any x, we find all y such that F(x) + F(y) + F(x+y) gives us
   * an element in the image set. We then add {x,y}, {x,x+y}, and {y,x+y} into the hash
   * map (we always add {a,b} with a < b)
   */


  //GHashTable * hash_pairs = g_hash_table_new(hash_pair, compare_pairs);
  for(size_t x = 1; x < N; ++x) {
    for(size_t y = x+1; y < N; ++y) {
      if(x != y) {
	size_t z = x^y;
	if(y < z) {
	  size_t v = f.vbf_tt_values[x] ^ f.vbf_tt_values[y] ^ f.vbf_tt_values[x^y];
	  if(PREDICTED_IMAGE_SET_MAP[v]) {
	    /* x and y */
	    add_compatible_pair(x,y);
	    add_compatible_pair(x,z);
	    add_compatible_pair(y,z);
	  }
	}
      }
    }
  }

  size_t ASSIGNMENTS [f.vbf_tt_dimension];

  vbf_tt T;
  T.vbf_tt_dimension = f.vbf_tt_dimension;
  T.vbf_tt_number_of_entries = N;
  T.vbf_tt_values = calloc(N, sizeof(size_t));


  guess_triple();

  free(T.vbf_tt_values);

  destroy_structures();
}

/* Check whether a given function is EA-equivalent to a triplicate function */
/* Returns trurth table of the triplicate function, or false */
int main(int argc, char ** argv) {
	if(argc != 2) {
		printf("Usage: %s TT_FILE\n", argv[0]);
		return 1;
	}

	vbf_tt f = load_vbf_tt_from_file(argv[1]);
	N = (1L << f.vbf_tt_dimension);
	F = &f;

	if(vbf_tt_is_3_to_1(f)) {
	  printf("True\n");
	  return 0;
	}

	is_equivalent_to_triplicate(f);
	if(!result_found) {
	  printf("False\n");
	}

	vbf_tt_destroy(f);

	return 0;
}
