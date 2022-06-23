#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "vbf.h"

_Bool get_bit(size_t * map, size_t index) {
  size_t byte_index = index / sizeof(size_t);
  size_t bit_index = index % sizeof(size_t);
  size_t mask = (1L << bit_index);
  return map[byte_index] & mask;
}

void set_bit(size_t * map, size_t index, _Bool value) {
  size_t byte_index = index / sizeof(size_t);
  size_t bit_index = index % sizeof(size_t);
  size_t mask = (1L << bit_index);
  if(!value) {
    map[byte_index] &= ~mask;
  }
  else {
    map[byte_index] |= mask;
  }
}

void vbf_tt_destroy(vbf_tt tt) {
  free(tt.vbf_tt_values);
}

void vbf_wt_destroy(vbf_wt tt) {
  for(size_t a = 0; a < DIM2SIZE(tt.vbf_walsh_table_dimension); ++a) {
    free(tt.vbf_walsh_table_values[a]);
  }
  free(tt.vbf_walsh_table_values);
}

vbf_tt load_vbf_tt_from_file(char const path[static 1]) {
  vbf_tt tt;
  tt.vbf_tt_dimension = 0;

  FILE * input_file = fopen(path, "r");
  if(!input_file) {
    perror("Could not open file.");
    return tt;
  }

  /* First line of file should contain dimension of finite field */
  size_t dimension;
  if (!fscanf(input_file, "%lu", &dimension)) {
      perror("Could not read dimension.");
  }
  else {
    tt.vbf_tt_dimension = dimension;
    size_t field_size = 1L << dimension;
    tt.vbf_tt_number_of_entries = field_size;
    tt.vbf_tt_values = malloc(tt.vbf_tt_number_of_entries * sizeof(vbf_tt_entry));

    for(size_t i = 0; i < tt.vbf_tt_number_of_entries; ++i) {
      fscanf(input_file, "%lu", &tt.vbf_tt_values[i]);
    }
  }

  fclose(input_file);

  return tt;
}

void vbf_tt_print_truth_table(vbf_tt tt) {
	printf("%lu\n", tt.vbf_tt_dimension);
	for(size_t i = 0; i < DIM2SIZE(tt.vbf_tt_dimension); ++i) {
		  printf("%lu ", tt.vbf_tt_values[i]);
	}
	printf("\n");
}

vbf_tt vbf_tt_copy(vbf_tt src) {
  vbf_tt copy = src;
  copy.vbf_tt_values = malloc( sizeof(vbf_tt_entry) * DIM2SIZE(src.vbf_tt_dimension) );
  memcpy(copy.vbf_tt_values, src.vbf_tt_values, sizeof(vbf_tt_entry) * DIM2SIZE(src.vbf_tt_dimension));
  return src;
}

void vbf_tt_compose(vbf_tt * dest, vbf_tt * src) {
  for (vbf_tt_entry x = 0; x < DIM2SIZE((*dest).vbf_tt_dimension); ++x) {
    (*dest).vbf_tt_values[x] = (*dest).vbf_tt_values[(*src).vbf_tt_values[x]];
  }
}

void vbf_tt_multiply_by_constant(vbf_tt tt, vbf_tt_entry c) {
  size_t n = tt.vbf_tt_dimension;
  vbf_tt_entry pp = vbf_tt_get_primitive_polynomial(n);
  for(size_t i = 0; i < tt.vbf_tt_number_of_entries; ++i) {
    tt.vbf_tt_values[i] = vbf_tt_ff_multiply( tt.vbf_tt_values[i], c, pp, n );
  }
}

void vbf_tt_add(vbf_tt to, vbf_tt from) {
  for(size_t i = 0; i < to.vbf_tt_number_of_entries; ++i) {
    to.vbf_tt_values[i] ^= from.vbf_tt_values[i];
  }
}


/* WALSH TRANSFORM */

_Bool dot(vbf_tt_entry a, vbf_tt_entry b) {
  return (POPCOUNT_FUNCTION(a & b) % 2);
}

long vbf_tt_walsh_transform(vbf_tt TT, vbf_tt_entry a, vbf_tt_entry b) {
  long sum = 0;

  for(vbf_tt_entry x = 0; x < DIM2SIZE(TT.vbf_tt_dimension); ++x) {
    sum += (dot(a,x) ^ dot(b,TT.vbf_tt_values[x])) ? -1 : 1;
  }

  return sum;
}

vbf_wt vbf_tt_to_wt(vbf_tt tt) {
  vbf_wt WT;
  size_t dimension = tt.vbf_tt_dimension;
  WT.vbf_walsh_table_dimension = dimension;
  WT.vbf_walsh_table_values = malloc( sizeof(vbf_walsh_table_entry *) * DIM2SIZE(dimension) );
  for(size_t a = 0; a < DIM2SIZE(dimension); ++a) {
    WT.vbf_walsh_table_values[a] = malloc( sizeof(vbf_walsh_table_entry) * DIM2SIZE(dimension) );
    for(size_t b = 0; b < DIM2SIZE(dimension); ++b) {
      WT.vbf_walsh_table_values[a][b] = (vbf_walsh_table_entry) vbf_tt_walsh_transform(tt,a,b);
    }
  }

  return WT;
}

void vbf_wt_print_walsh_table(vbf_wt wt) {
  size_t entries = DIM2SIZE(wt.vbf_walsh_table_dimension);
  for (size_t a = 0; a < entries; ++a) {
    for(size_t b = 0; b < entries; ++b) {
      printf("%ld\t", wt.vbf_walsh_table_values[a][b]);
    }
    printf("\n");
  }
}

long vbf_wt_power_moment(vbf_wt WT, short unsigned k, vbf_tt_entry shift_a, vbf_tt_entry shift_b) {
  long sum = 0;
  for(size_t a = 0; a < DIM2SIZE(WT.vbf_walsh_table_dimension); ++a) {
    for(size_t b = 0; b < DIM2SIZE(WT.vbf_walsh_table_dimension); ++b) {
      long modifier = (dot(a,shift_a) ^ dot(b,shift_b)) ? -1 : 1;
      long base = WT.vbf_walsh_table_values[a][b];
      long product = 1;
      for(short unsigned i = 0; i < k; ++i) {
	product *= base;
      }
      sum += product * modifier;
    }
  }
  return sum;
}


/* EA-algorithm */
void ea_partition_print(partition p) {
  for(size_t c = 0; c < p.partition_number_of_classes; ++c) {
    printf("%lu (%lu): ", c+1, p.partition_class_sizes[c]);
    /* Last item processed separately to add comma */
    for(size_t j = 0; j < p.partition_class_sizes[c]-1; ++j) {
      printf("%ld, ", p.partition_classes[c][j]);
    }
    printf("%ld", p.partition_classes[c][p.partition_class_sizes[c]-1]);
    printf("\n");
  }
}

void ea_partition_destroy(partition p) {
  for(size_t c = 0; c < p.partition_number_of_classes; ++c) {
    free(p.partition_classes[c]);
  }
  free(p.partition_classes);
  free(p.partition_class_sizes);
}

int compare_size_t(const void* a, const void* b) {
  size_t x1 = *(const size_t*) a;
  size_t x2 = *(const size_t*) b;

  if (x1 < x2) { return -1; }
  if (x1 > x2) { return 1; }
  return 0;
}

void ea_partition_4(vbf_tt TT) {
  /* Go over all triples of elements (x1,x2,x3); repetitions are allowed for simplicity. For every triple
   * we take x4 = x1 + x2 + x3, then find F(x1) + F(x2) + F(x3) + F(x4). A counter corresponding to the
   * value defined by this sum is incremented. The elements of the finite field are then partitioned
   * according to the values of their associated counters.
   */
  size_t multiplicities [DIM2SIZE(TT.vbf_tt_dimension)];
  size_t possible_values [DIM2SIZE(TT.vbf_tt_dimension)];

  for(size_t i = 0; i < TT.vbf_tt_number_of_entries; ++i) {
    multiplicities[i] = 0;
  }

  for(size_t x1 = 0; x1 < TT.vbf_tt_number_of_entries; ++x1) {
    for(size_t x2 = 0; x2 < TT.vbf_tt_number_of_entries; ++x2) {
      for(size_t x3 = 0; x3 < TT.vbf_tt_number_of_entries; ++x3) {
	size_t x4 = x1 ^ x2 ^ x3;
	size_t w = TT.vbf_tt_values[x1] ^ TT.vbf_tt_values[x2] ^ TT.vbf_tt_values[x3] ^ TT.vbf_tt_values[x4];
	++multiplicities[w];
      }
    }
  }

  /* At this point, we know how many times each element of the finite field occurs.
   * We now want to compute how many times each number of occurrences is encountered.
   * We first sort the sequence of multiplicities in place.
   */
  qsort(multiplicities, TT.vbf_tt_number_of_entries, sizeof(size_t), compare_size_t);

  /* We now count how many times each multiplicity occurs, and record this in the
   * possible_values array, to be sorted and recorded into the partition later
   */
  size_t position = 1;
  size_t current_value = multiplicities[0];
  size_t current_count = 1;
  size_t current_record_position = 0;
  while(position < TT.vbf_tt_number_of_entries) {
    if(multiplicities[position] != current_value) {
      possible_values[current_record_position++] = current_count;
      current_value = multiplicities[position];
      current_count = 1;
    }
    else {
      ++current_count;
    }

    ++position;
  }

  possible_values[current_record_position++] = current_count;
  qsort(possible_values, current_record_position, sizeof(size_t), compare_size_t);

  for(size_t i = 0; i < current_record_position; ++i) {
    printf("%lu ", possible_values[i]);
  }
  printf("\n");
}



partition ea_partition_walsh(vbf_wt WT, short unsigned k) {
  size_t multiplicities [DIM2SIZE(WT.vbf_walsh_table_dimension)];
  size_t possible_values [DIM2SIZE(WT.vbf_walsh_table_dimension)];
  size_t current_possible_value = 0;

  for(size_t s = 0; s < DIM2SIZE(WT.vbf_walsh_table_dimension); ++s) {
    size_t walsh = vbf_wt_power_moment(WT, k, 0, s);
    /* Note that the value of the power moment is 2^(2*n) times the multiplicity */
    size_t multiplicity = walsh >> (2*WT.vbf_walsh_table_dimension);
    multiplicities[s] = multiplicity;
    /* Try to find this multiplicity in the list of recorded multiplicities; if it is not there, add a new entry */
    size_t k = 0;
    for( ; k < current_possible_value; ++k) {
      if (possible_values[k] == multiplicity) {
	break;
      }
    }
    if (k == current_possible_value) {
      possible_values[current_possible_value++] = multiplicity;
    }
  }

  /* At this point, we know what exact multiplicities define the partition, and can construct the structure */
  partition p;
  p.partition_dimension = WT.vbf_walsh_table_dimension;
  p.partition_number_of_classes = current_possible_value;
  p.partition_class_sizes = malloc( sizeof(size_t) * current_possible_value );
  p.partition_classes = malloc( sizeof(vbf_tt_entry *) * current_possible_value);

  vbf_tt_entry current_class [DIM2SIZE(WT.vbf_walsh_table_dimension)];
  size_t current_class_index;

  for(size_t class_index = 0; class_index < current_possible_value; ++class_index) {
    current_class_index = 0;
    for(size_t s = 0; s < DIM2SIZE(WT.vbf_walsh_table_dimension); ++s) {
      if(multiplicities[s] == possible_values[class_index]) {
	current_class[current_class_index++] = s;
      }
    }
    p.partition_class_sizes[class_index] = current_class_index;
    p.partition_classes[class_index] = malloc( sizeof(vbf_tt_entry) * current_class_index );
    memcpy(p.partition_classes[class_index], current_class, sizeof(vbf_tt_entry) * current_class_index);
  }

  return p;
}

fseq findMaximalLinearlyIndependentSubset(fseq subset) {
	printf("%lu\n", subset.field_sequence_dimension);
	printf("%lu\n", subset.field_sequence_length);
	for(size_t i = 0; i < subset.field_sequence_length; ++i) {
		printf("%lu ", subset.field_sequence_values[i]);
	}
	printf("\n");

	fseq result;
	result.field_sequence_dimension = subset.field_sequence_dimension;

	vbf_tt_entry constructed_set [subset.field_sequence_dimension];
	size_t count = 0;

	/* Array of flags determining which elements have already been generated */
	_Bool generated_flags [DIM2SIZE(subset.field_sequence_dimension)];
	/* Actual list of generated elements, for the sake of more efficiently updating the flags */
	vbf_tt_entry generated [DIM2SIZE(subset.field_sequence_dimension)];
	generated[0] = 0;
	size_t number_generated = 1; //zero element

	generated_flags[0] = true;
	for (size_t j = 1; j < DIM2SIZE(subset.field_sequence_dimension); ++j) {
		generated_flags[j] = false;
	}

	/* Exhaustive search: go through all elements of the given subset, making sure that the element is not already geneated using the flag array; note that here we do not demand that the linear combinations of elements of this set be in the given subset */
	for(size_t i = 0; i < subset.field_sequence_length; ++i) {
		vbf_tt_entry element = subset.field_sequence_values[i];
		if (!generated_flags[element]) {
			constructed_set[count++] = element;
			size_t old_number_generated = number_generated; /* otherwise, we are modfiyng the control variable of the loop, and weird things happen */
			for(size_t k = 0; k < old_number_generated; ++k) {
				vbf_tt_entry new_element = generated[k] ^ element;
				generated_flags[ generated[k] ^ element ] = true;
				generated[ number_generated++ ] = (generated[k] ^ element);
			}

			if(count == subset.field_sequence_dimension) {
				break;
			}
		}
	}


	/* Fill in data into the field_sequence struct and return */
	result.field_sequence_length = count;
	result.field_sequence_values = malloc( sizeof(vbf_tt_entry) * count );
	memcpy(result.field_sequence_values, constructed_set, sizeof(vbf_tt_entry) * count);

	return result;
}

fseq field_sequence_complement(fseq fs) {
  size_t entries = DIM2SIZE(fs.field_sequence_dimension);
  fseq result;
  result.field_sequence_dimension = fs.field_sequence_dimension;
  result.field_sequence_length = entries - fs.field_sequence_length;
  result.field_sequence_values = malloc(sizeof(vbf_tt_entry) * result.field_sequence_length);

  _Bool map [entries];
  for(size_t i = 0; i < entries; ++i) {
    map[i] = false;
  }
  for(size_t i = 0; i < fs.field_sequence_length; ++i) {
    map[fs.field_sequence_values[i]] = true;
  }

  size_t g = 0;
  for(size_t x = 0; x < entries; ++x) {
    if(!map[x]) {
      result.field_sequence_values[g++] = x;
    }
  }

  return result;
}

int field_sequence_compare(const void * a, const void * b) {
  size_t l1 = (*( (fseq *) a )).field_sequence_length;
  size_t l2 = (*( (fseq *) b )).field_sequence_length;
  if( l1 != l2 ) {
    return (l1 < l2) ? -1 : 1;
  }

  for(size_t i = 0; i < l1; ++i) {
    vbf_tt_entry e1 = (*( (fseq *) a )).field_sequence_values[i];
    vbf_tt_entry e2 = (*( (fseq *) b )).field_sequence_values[i];
    if (e1 != e2) {
      return (e1 < e2) ? -1 : 1;
    }
  }

  return 0;
}

void field_sequence_destroy(fseq fs) {
	free(fs.field_sequence_values);
}

void field_sequence_add_constant(fseq fs, size_t c) {
  for(size_t i = 0; i < fs.field_sequence_length; ++i) {
    fs.field_sequence_values[i] ^= c;
  }
}

size_t ea_find_outer_permutations_preserving_partition(partition p, fseq ** output) {
  size_t entries = DIM2SIZE(p.partition_dimension);

  size_t BLOCK_SIZE = entries; /* amount of cells by which the output partition will be expanded if necessary */
  size_t TOTAL_SIZE = BLOCK_SIZE;

  (*output) = malloc( sizeof(fseq) * BLOCK_SIZE );
  size_t count = 0;

  /* First, we convert the partition into an indexed array P, such that P[x] is an integer giving the class of x in the partition */
  short unsigned P [entries];
  for(size_t c = 0; c < p.partition_number_of_classes; ++c) {
    for(size_t j = 0; j < p.partition_class_sizes[c]; ++j) {
      P[p.partition_classes[c][j]] = c;
    }
  }

  /* Now, the integer value X of any element in the finite field exactly corresponds to its coordinates w.r.t. the standard basis.
   * Next, we perform an exhaustive search by attempting all possible assignments of images to the elements in the basis; after assigning
   * images to the first K basis elements, we can loop through all numbers between 0 and 2^k, which will represent the elements of the
   * field expressible using those basis elements. For each element, we add the images corresponding to its coordinates, and check whether
   * their sum belongs to the same class as the original element. If not, we backtrack.
   */

  vbf_tt_entry basis_images [p.partition_dimension];
  for(size_t i = 0; i < p.partition_dimension; ++i) {
    basis_images[i] = 1;
  }
  vbf_tt_entry all_images [entries];
  all_images[0] = 0;
  _Bool generated [entries]; /* flags for only selecting images outside of the generated subspace */
  generated[0] = true;
  for(size_t i = 1; i < entries; ++i) {
    generated[i] = false;
  }

  size_t i = 0; /* index of the basis element to which we are currently assigning an image */
  while(true) { /* We will manually break once the BASIS[0] exceeds the field size */
    outerLoop: /* I'm sorry... */
    //printf("I:%lu\n", i);
    for(vbf_tt_entry vi = basis_images[i]; vi < entries; ++vi) { /* NB: if we go one level deeper, this loop will terminate prematurely, and will be resumed upon backtracking */
      /* Skip already generated elements (permutation) */
      if(generated[vi]) {
	continue;
      }

      /* Skip elements from a different class than BASIS[i] itself */
      if(P[vi] != P[(1L << i)]) {
	continue;
      }

      /* At this point, we attempt to assign BASIS[i] |-> vi */

      /* Generate all elements that involve the new element: go through all elements that are already generated, and add vi to their images
       * to obtain an updated set; if the first K elements of the basis have been assigned images, then we know the images of the elements
       * between 0 and 2^K-1 (inclusive)
       */
      vbf_tt_entry new_preimage;
      vbf_tt_entry new_image;

      for(vbf_tt_entry pg = 0; pg < (1L << i); ++pg) {
	new_preimage = pg ^ (1L << i);
	new_image = all_images[pg] ^ vi;

	/* Make sure the partition is preserved */
	if(P[new_preimage] != P[new_image]) {
	  break;
	}

	/* If we are assigning the last basis image, we do not need to keep track of the generated elements, since all of them
	 * will be generated; furthermore, this absolves us from the need to reset the generated[x] flags when backtracking
	 * after a successfully found permutation
	 */
	if(i < p.partition_dimension - 1) {
	  generated[new_image] = true;
	  all_images[new_preimage] = new_image;
	}
      }

      /* If there were no conflicts, try to go one level deeper */
      if(P[new_preimage] == P[new_image]) {
	//printf("Going deeper\n");
	basis_images[i++] = vi;

	/* If all basis images have been assigned, we have found a permutation */
	if(i >= p.partition_dimension) {
	  (*output)[count].field_sequence_dimension = p.partition_dimension;
	  (*output)[count].field_sequence_length = p.partition_dimension;
	  (*output)[count].field_sequence_values = malloc( sizeof(vbf_tt_entry) * p.partition_dimension );
	  memcpy((*output)[count].field_sequence_values, basis_images, sizeof(vbf_tt_entry) * p.partition_dimension);
	  ++count;

	  /* Allocate more memory, if necessary */
	  if(count >= TOTAL_SIZE) {
	    TOTAL_SIZE += BLOCK_SIZE;
	    fseq * new_output = realloc( (*output), sizeof(fseq) * TOTAL_SIZE );
	    if(new_output) {
	      (*output) = new_output;
	    }
	    else {
	      //TODO
	      //Handle lack of memory issues somehow
	    }
	  }
	  ++basis_images[--i]; /* try out other values, if possible */
	}
	goto outerLoop;
      }

      /* At this point, we proceed to the next possible value of a basis image, so we need to clear
       * the generated[x] flags induced by the previous choice for BASIS[i] */
      for(vbf_tt_entry pg = 0; pg < (1L << i); ++pg) {
	new_image = all_images[pg] ^ vi;
	generated[new_image] = false;
      }

      /* We now go to the next iteration of the "for" loop, which will try out all remaining values for BASIS[i] */
      ++basis_images[i];
    }

    /* If we have reached this point, then all possible values for BASIS[i] have been exhausted. We reset the value for BASIS[i]
     * and go back to BASIS[i-1]; if i = 0, then the exhaustive search is concluded
     */
    if(!i) {
      break;
    }

    //printf("Backtracking again\n");
    basis_images[i] = 1;

    /* Reset all generated[x] flags for elements using BASIS[i-1] */
    for(vbf_tt_entry pg = 0; pg < (1L << (i-1)); ++pg) {
	vbf_tt_entry new_image = all_images[pg] ^ basis_images[i-1];
	generated[new_image] = false;
    }
    ++basis_images[i-1];
    --i;
  }

  return count;
}

void ea_find_union_of3t(vbf_tt f, _Bool *** output) {
  size_t entries = DIM2SIZE(f.vbf_tt_dimension);
  (*output) = malloc(sizeof(_Bool * ) * entries);
  for(size_t i = 0; i < entries; ++i) {
    (*output)[i] = malloc(sizeof(_Bool) * entries);
    for(size_t j = 0; j < entries; ++j) {
      (*output)[i][j] = false;
    }
  }

  for(vbf_tt_entry x = 0; x < entries; ++x) {
    for(vbf_tt_entry y = 0; y < entries; ++y) {
      vbf_tt_entry t = f.vbf_tt_values[x] ^ f.vbf_tt_values[y] ^ f.vbf_tt_values[x^y];
      (*output)[t][x] = true;
      (*output)[t][y] = true;
      (*output)[t][x^y] = true;
    }
  }
}

fseq ea_compute_domain(vbf_tt f, vbf_tt g, _Bool ** of3t_table, vbf_tt_entry x) {
  /* Go through all possible pairs (x,y,x+y) involving x; for each, compute t = G(x) + G(y) + G(x+y), and intersect the union of O^F_3(t) with the domain */
  size_t entries = DIM2SIZE(f.vbf_tt_dimension);
  _Bool domain [entries];
  for(size_t i = 0; i < entries; ++i) {
    domain[i] = true; /* initally, the domain contains all elements of the field */
  }

  vbf_tt_entry gx = g.vbf_tt_values[x];

  for(size_t y = 0; y < entries; ++y) {
    vbf_tt_entry t = gx ^ g.vbf_tt_values[y] ^ g.vbf_tt_values[x^y];
    for(size_t j = 0; j < entries; ++j) {
      domain[j] = domain[j] & of3t_table[t][j];
    }
  }

  /* Count remaining elements */
  size_t count = 0;
  for(size_t j = 0; j < entries; ++j) {
    count += domain[j];
  }

  /* Format result and return */
  fseq result;
  result.field_sequence_dimension = f.vbf_tt_dimension;
  result.field_sequence_length = count;
  result.field_sequence_values = malloc( sizeof(vbf_tt_entry) * count );
  size_t i = 0;
  for(size_t j = 0; j < entries; ++j) {
    if(domain[j]) {
      result.field_sequence_values[i++] = j;
    }
  }
  
  return result;
}

fseq ea_get_standard_basis(size_t dimension) {
  fseq result;
  result.field_sequence_dimension = dimension;
  result.field_sequence_length = dimension;
  result.field_sequence_values = malloc( sizeof(vbf_tt_entry) * dimension );
  for(size_t i = 0; i < dimension; ++i) {
    result.field_sequence_values[i] = (1L << i);
  }
  return result;
}

fseq ea_get_basis_map(fseq basis) {
  fseq result;
  size_t entries = DIM2SIZE(basis.field_sequence_dimension);
  result.field_sequence_dimension = basis.field_sequence_dimension;
  result.field_sequence_length = entries;
  result.field_sequence_values = malloc( sizeof(vbf_tt_entry) * entries );
  for(size_t x = 0; x < entries; ++x) {
    size_t y = 0;
    for(size_t j = 0; j < basis.field_sequence_dimension; ++j) {
      if( (1L << j) & x ) {
	y ^= basis.field_sequence_values[j];
      }
    }
    result.field_sequence_values[x] = y;
  }
  return result;
}

fseq ea_find_inner_permutation(vbf_tt f, vbf_tt g, fseq basis, fseq * domains) {
  printf("FIX BASIS MAPPING\n"); //So I don't forget to

  size_t dimension = f.vbf_tt_dimension;
  size_t entries = DIM2SIZE(dimension);

  size_t positions [dimension];
  for(size_t i = 0; i < dimension; ++i) {
    positions[i] = 0;
  }

  vbf_tt_entry basis_images [dimension];
  vbf_tt_entry L_images [entries];
  vbf_tt_entry L2_images [entries];
  L_images[0] = 0;
  L2_images[0] = 0;

  fseq result;
  result.field_sequence_dimension = 0; /* to indicate failure if returned */

  fseq basis_map = ea_get_basis_map(basis);

  size_t i = 0;
  while(true) {
    /* If all basis images have been successfully assigned, we are finished, so leave the loop */

    if(i >= f.vbf_tt_dimension) {
      break;
    }

    /* If we have exhausted all possibilities for the current variable, backtrack one level if possible, otherwise abort */
    if(positions[i] >= domains[i].field_sequence_length) {
      if(i) {
	positions[i] = 0;
	++positions[--i];
	continue;
      }

      /* If we have reached this point, we have exhausted all values for BASIS[0] without finding anything, so we fail; we break so
       * that data is cleaned up in one place (after the end of the loop)
       */
      break;
    }

    /* Attempt to assign domains[i][positions[i]] to BASIS[i] */
    vbf_tt_entry basis_image_l2 = basis_images[i] = domains[i].field_sequence_values[positions[i]];
    vbf_tt_entry basis_image_l = f.vbf_tt_values[basis_image_l2] ^ g.vbf_tt_values[basis.field_sequence_values[i]];

    /* Generate all elements of L2 and L that can be generated using the currently available basis images, and assert
     * that the values of the two functions are compatible
     */
    _Bool problem = false;
    for(size_t prex = 0; prex < (1L <<i); ++prex) {
      //TODO: Map between standard basis and new basis
      vbf_tt_entry x = prex;
      vbf_tt_entry new_value_l2 = L2_images[x] ^ basis_image_l2;
      vbf_tt_entry new_value_l_alpha = L_images[x] ^ basis_image_l;
      vbf_tt_entry new_value_l_beta = f.vbf_tt_values[new_value_l2] ^ g.vbf_tt_values[x^basis.field_sequence_values[i]];
      if (new_value_l_alpha != new_value_l_beta) {
	problem = true;
	break;
      }
      L_images[x ^ basis.field_sequence_values[i]] = new_value_l_alpha;
      L2_images[x ^ basis.field_sequence_values[i]] = new_value_l2;
    }

    if(!problem) {
      /* If we are here, then no contradiction has been found, and we can move on to the next variable (for now). */
      ++i;
      continue;
    }

    /* If we are here, something was wrong with the last choice for BASIS[i]; so we move on to the next one (if available) */
    ++positions[i];
  }

  field_sequence_destroy(basis_map);

  /* If the value of i is equal to the dimension, then we have successfully assigned everything, so we set up the result sequence */
  result.field_sequence_dimension = f.vbf_tt_dimension;
  result.field_sequence_length = f.vbf_tt_dimension;
  result.field_sequence_values = malloc( sizeof(vbf_tt_entry) * result.field_sequence_dimension );
  memcpy(result.field_sequence_values, basis_images, sizeof( vbf_tt_entry ) * result.field_sequence_dimension );

  /* Successful or otherwise, we return the struct; if its dimension is 0, this will indicate failure; otherwise, it will contain
   * a basis image defining L2
   */
  return result;
}

vbf_tt tt_orthoderivative(vbf_tt f) {
	vbf_tt od;
	od.vbf_tt_dimension = f.vbf_tt_dimension;
	od.vbf_tt_number_of_entries = (1L << od.vbf_tt_dimension);
	od.vbf_tt_values = malloc( sizeof(vbf_tt_entry) * od.vbf_tt_number_of_entries );

	/* Compute each element of the ortho-derivative manually: o(a) must be such that
	 * the dot product o(a) * (F(x) + F(a+x) + F(a) + F(0)) is equal to 0 for all x.
	 */
	od.vbf_tt_values[0] = 0;
	_Bool problem = false;

	for(vbf_tt_entry a = 1; a < od.vbf_tt_number_of_entries; ++a) {
		for(size_t possible_value = 1; possible_value < od.vbf_tt_number_of_entries; ++possible_value) {
			problem = false;
			for(size_t x = 0; x < od.vbf_tt_number_of_entries; ++x) {
				vbf_tt_entry derivative = f.vbf_tt_values[0] ^ f.vbf_tt_values[a] ^ f.vbf_tt_values[x] ^ f.vbf_tt_values[x^a];
				if (dot(possible_value, derivative)) {
					problem = true;
					break;
				}
			}
			if (!problem) {
				od.vbf_tt_values[a] = possible_value;
				break;
			}
		}
	}

	return od;
}

vbf_tt random_linear_permutation(size_t dimension) {
  size_t entries = DIM2SIZE(dimension);

  _Bool generated [entries]; /* so we do not assign an element that has already been generated as a value */
  vbf_tt_entry list_generated [entries];
  generated[0] = true;
  for(size_t i = 1; i < entries; ++i) {
    generated[i] = false;
  }
  list_generated[0] = 0;

  size_t basis_images [dimension];
  for(size_t i = 0; i < dimension; ++i) {
    size_t j = rand() % entries;
    while(generated[j]) {
      j = (j + 1) % entries;
    }
    basis_images[i] = j; /* note that i already gets incremented by the for loop */
    for(size_t k = 0; k < (1L << (i)); ++k) {
      list_generated[ (1L << (i)) + k ] = list_generated[k] ^ j;
      generated[ list_generated[k] ^ j ] = true;
    }
  }

  vbf_tt result;
  result.vbf_tt_dimension = dimension;
  result.vbf_tt_number_of_entries = DIM2SIZE(dimension);
  result.vbf_tt_values = malloc( sizeof(vbf_tt_entry) * entries );
  memcpy(result.vbf_tt_values, list_generated, sizeof(vbf_tt_entry) * entries);
  return result;
}

vbf_tt random_linear_function(size_t dimension) {
  size_t entries = DIM2SIZE(dimension);

  vbf_tt_entry list_generated [entries];
  list_generated[0] = 0;

  size_t basis_images [dimension];
  for(size_t i = 0; i < dimension; ++i) {
    size_t j = rand() % entries;
    basis_images[i] = j; /* note that i already gets incremented by the for loop */
    for(size_t k = 0; k < (1L << (i)); ++k) {
      list_generated[ (1L << (i)) + k ] = list_generated[k] ^ j;
    }
  }

  vbf_tt result;
  result.vbf_tt_dimension = dimension;
  result.vbf_tt_number_of_entries = DIM2SIZE(dimension);
  result.vbf_tt_values = malloc( sizeof(vbf_tt_entry) * entries );
  memcpy(result.vbf_tt_values, list_generated, sizeof(vbf_tt_entry) * entries);
  return result;
}

fseq random_linear_subspace(size_t dimension, size_t subspace_dimension) {
  /* Select a random basis for the subspace, generate the elements, and return their sequence */
  _Bool generated[DIM2SIZE(dimension)];
  vbf_tt_entry list_generated [(1L << subspace_dimension)];
  generated[0] = true;
  for(size_t i = 1; i < DIM2SIZE(dimension); ++i) {
    generated[i] = false;
  }
  list_generated[0] = 0;
  vbf_tt_entry basis [subspace_dimension];
  size_t g = 0;

  while(g < subspace_dimension) {
    vbf_tt_entry r = rand() % DIM2SIZE(dimension);
    while(generated[r]) {
      r = (r + 1) % DIM2SIZE(dimension);
    }
    
    size_t cutoff = (1L << g++);
    for(size_t j = 0; j < cutoff; ++j) {
      vbf_tt_entry new_element = list_generated[j] ^ r;
      list_generated[cutoff+j] = new_element;
      generated[new_element] = true;
    }
  }

  fseq result;
  result.field_sequence_dimension = dimension;
  result.field_sequence_length = DIM2SIZE(subspace_dimension);
  result.field_sequence_values = malloc( sizeof(vbf_tt_entry) * DIM2SIZE(subspace_dimension) );
  memcpy(result.field_sequence_values, list_generated, sizeof(vbf_tt_entry) * DIM2SIZE(subspace_dimension) );

  return result;
}

_Bool vbf_tt_is_linear(vbf_tt f) {
  for(vbf_tt_entry x = 0; x < DIM2SIZE(f.vbf_tt_dimension); ++x) {
    for(vbf_tt_entry y = 0; y < DIM2SIZE(f.vbf_tt_dimension); ++y) {
      if( (f.vbf_tt_values[x] ^ f.vbf_tt_values[y]) != f.vbf_tt_values[x^y]) {
	printf("F[%lu] = %lu, F[%lu] = %lu, F[%lu] = %lu\n", x, f.vbf_tt_values[x], y, f.vbf_tt_values[y], x^y, f.vbf_tt_values[x^y]);
	return false;
      }
    }
  }
  return true;
}

_Bool vbf_tt_is_permutation(vbf_tt f) {
  size_t entries = DIM2SIZE(f.vbf_tt_dimension);
  _Bool targets [entries];
  for(size_t i = 0; i < entries; ++i) {
    targets[i] = false;
  }
  for(vbf_tt_entry x = 0; x < entries; ++x) {
    vbf_tt_entry image = f.vbf_tt_values[x];
    if (targets[image]) {
      return false;
    }
    targets[image] = true;
  }
  return true;
}

fseq vbf_wt_bent_components(vbf_wt WT) {
  /* A function is bent if its Walsh tranform only takes two values, viz. 2^(n/2) or its additive inverse. For the Walsh transform of a VBF, W_F(a,b)
   * is the Walsh transform of the component function F_b at a. Thus, we go through all possible b's, and check whether all Walsh values are 2^(n/2)
   * in absolute value.
   */
  assert(WT.vbf_walsh_table_dimension % 2 == 0);
  size_t entries = DIM2SIZE(WT.vbf_walsh_table_dimension); /* bent functions exist only for even extension degrees */
  vbf_tt_entry bent [entries];
  size_t found = 0;

  vbf_walsh_table_entry target_value = (1L << (WT.vbf_walsh_table_dimension / 2));

  for(vbf_tt_entry b = 0; b < entries; ++b) {
    _Bool can_be_bent = true;
    for(vbf_tt_entry a = 0; a < entries; ++a) {
      if( (WT.vbf_walsh_table_values[a][b] != target_value) && (WT.vbf_walsh_table_values[a][b] != -target_value) ) {
	can_be_bent = false;
	break;
      }
    }
    if(can_be_bent) {
      bent[found++] = b;
    }
  }

  fseq result;
  result.field_sequence_dimension = WT.vbf_walsh_table_dimension;
  result.field_sequence_length = found;
  result.field_sequence_values = malloc( sizeof(vbf_tt_entry) * found );
  memcpy(result.field_sequence_values, bent, sizeof(vbf_tt_entry) * found );
  return result;
}

fseq vbf_tt_nonbent_components(vbf_tt TT) {
  assert(TT.vbf_tt_dimension % 2 == 0);
  size_t entries = DIM2SIZE(TT.vbf_tt_dimension); /* bent functions exist only for even extension degrees */
  vbf_tt_entry bent [entries];
  size_t found = 0;

  /* All Walsh coefficients W(a,b) for all a should be equal to the following target value in
   * order for Fb to be bent.
   */
  vbf_walsh_table_entry target_value = (1L << (TT.vbf_tt_dimension / 2));

  for(vbf_tt_entry b = 0; b < entries; ++b) {
    _Bool can_be_bent = true;
    for(vbf_tt_entry a = 0; a < entries; ++a) {
      long walsh_coefficient = vbf_tt_walsh_transform(TT, a, b);
      if( (walsh_coefficient != target_value) && (walsh_coefficient != -target_value) ) {
	can_be_bent = false;
	break;
      }
    }
    if(!can_be_bent) {
      bent[found++] = b;
    }
  }

  fseq result;
  result.field_sequence_dimension = TT.vbf_tt_dimension;
  result.field_sequence_length = found;
  result.field_sequence_values = malloc( sizeof(vbf_tt_entry) * found );
  memcpy(result.field_sequence_values, bent, sizeof(vbf_tt_entry) * found );
  return result;
}

fseq smallest_basis(fseq subspace) {
  /* Note that we blindly assume the given subspace is indeed a subspace,
   * and that it is sorted
   */
  size_t dimension = subspace.field_sequence_dimension;
  size_t l = subspace.field_sequence_length;

  /* Ad-hoc binary logarithm for exact powers of 2*/
  size_t subspace_dimension = 0;
  size_t i = 1;
  while(i < l) {
    ++subspace_dimension;
    i <<= 1;
  }
  vbf_tt_entry basis [dimension];
  _Bool generated [DIM2SIZE(dimension)];
  generated[0] = true;
  vbf_tt_entry list_generated [l];
  list_generated[0] = 0;
  for(size_t i = 1; i < DIM2SIZE(dimension); ++i) {
    generated[i] = false;
  }

  /* Since we assume that the given sequence of elements is sorted, we simply
   * loop through all available elements, and take ones that are linearly independent
   * on the previously selected ones
   */
  size_t g = 0;
  for(size_t i = 0; i < l; ++i) {
    vbf_tt_entry x = subspace.field_sequence_values[i];
    if(!generated[x]) {
      basis[g] = x;
      size_t cutoff = (1L << (g++));
      if(g >= dimension) {
	break;
      }
      for(size_t j = 0; j < cutoff; ++j) {
	list_generated[cutoff + j] = list_generated[j] ^ x;
	generated[list_generated[j] ^ x] = true;
      }
    }
  }

  fseq result;
  result.field_sequence_dimension = dimension;
  result.field_sequence_length = subspace_dimension;
  result.field_sequence_values = malloc( sizeof(vbf_tt_entry) * dimension );
  memcpy(result.field_sequence_values, basis, sizeof(vbf_tt_entry) * dimension);

  return result;
}

/* For sorting arrays of field elements */
int vbf_tt_compare(const void * a, const void *b) {
  vbf_tt_entry va = *((vbf_tt_entry *) a);
  vbf_tt_entry vb = *((vbf_tt_entry *) b);
  return (va > vb);
}

size_t find_2d_subspaces(fseq S, fseq ** output) {
  size_t BLOCK_SIZE = 2*DIM2SIZE(S.field_sequence_dimension);
  size_t TOTAL_SIZE = BLOCK_SIZE;
  size_t current_block = 0;

  size_t dimension = S.field_sequence_dimension;
  size_t entries = DIM2SIZE(dimension);
  _Bool set_map [entries];
  for(vbf_tt_entry i = 0; i < entries; ++i) {
    set_map[i] = false;
  }
  for(size_t i = 0; i < S.field_sequence_length; ++i) {
    set_map[S.field_sequence_values[i]] = true;
  }

  (*output) = malloc( sizeof(fseq) * BLOCK_SIZE );

  /* Blindly go through all distinct pairs of non-zero elements, verify that their XOR is in the set,
   * and record the entire 4-element sets.
   */
  for(size_t i1 = 0; i1 < S.field_sequence_length; ++i1) {
    vbf_tt_entry x = S.field_sequence_values[i1];
    for(size_t i2 = i1 + 1; i2 < S.field_sequence_length; ++i2) {
      vbf_tt_entry y = S.field_sequence_values[i2];
      vbf_tt_entry z = x^y;
      if(x < z && y < z && set_map[z]) {
	(*output)[current_block].field_sequence_dimension = dimension;
	(*output)[current_block].field_sequence_length = 4;
	(*output)[current_block].field_sequence_values = malloc(sizeof(vbf_tt_entry) * 4);
	(*output)[current_block].field_sequence_values[0] = 0;
	(*output)[current_block].field_sequence_values[1] = x;
	(*output)[current_block].field_sequence_values[2] = y;
	(*output)[current_block].field_sequence_values[3] = z;
	qsort((*output)[current_block].field_sequence_values, 4, sizeof(vbf_tt_entry), vbf_tt_compare);
	++current_block;

	if(current_block >= TOTAL_SIZE) {
	  TOTAL_SIZE += BLOCK_SIZE;
	  (*output) = realloc((*output), sizeof(fseq) * TOTAL_SIZE);
	}
      }
    }
  }

  return current_block;
}

size_t expand_subspaces(fseq S, fseq * input, size_t input_size, fseq ** output) {
  /* For every subspace M and every element x not in M, generate the coset M + x, see if it's contained in S,
   * and record the resulting subspace if so
   */

  size_t BLOCK_SIZE = 2*DIM2SIZE(S.field_sequence_dimension);
  size_t TOTAL_SIZE = BLOCK_SIZE;
  size_t current_block = 0;

  size_t dimension = S.field_sequence_dimension;
  size_t entries = DIM2SIZE(dimension);
  _Bool set_map [entries];
  for(vbf_tt_entry i = 0; i < entries; ++i) {
    set_map[i] = false;
  }
  for(size_t i = 0; i < S.field_sequence_length; ++i) {
    set_map[S.field_sequence_values[i]] = true;
  }

  (*output) = malloc( sizeof(fseq) * BLOCK_SIZE );

  size_t input_block_size = input[0].field_sequence_length; /* size of one input block */

  vbf_tt_entry coset [input_block_size];

  /* Certain entries from S will be forbidden for a given M, either because they are already in M, or
   * because they are already contained in a coset M + x for some prevously processed element x
   */
  _Bool forbidden [entries];

  for(size_t j1 = 0; j1 < input_size; ++j1) {
    vbf_tt_entry * M = input[j1].field_sequence_values;

    /* The index of forbidden elements is freshly computed for each subspace M */
    memcpy(forbidden, set_map, sizeof(_Bool) * entries );
    for(size_t i = 0; i < input_block_size; ++i) {
      forbidden[M[i]] = false; /* forbid elements already in M */
    }

    for(size_t i1 = 0; i1 < S.field_sequence_length; ++i1) {
      vbf_tt_entry x = S.field_sequence_values[i1];
      if(!forbidden[x]) { /* skip forbidden elements -- ones already in M, and ones belonging to previously generated cosets of M */
	continue;
      }

      /* We generate the coset M + x and check whether x does not already belong
       * to M, and whether all coset elements are in S, at the same time
       */
      _Bool problem = false;
      for(size_t k = 0; k < input_block_size; ++k) {
	if (x == M[k] || !set_map[M[k] ^ x]) {
	  problem = true;
	  break;
	}
	coset[k] = M[k] ^ x;
	forbidden[M[k] ^ x] = false; /* forbid the newly generated elements from being taken again */
      }

      if(problem) {
	continue;
      }

      /* If we're here, then we know that:
       * 1)x is not in M, so that M+x and M are distinct;
       * 2)M+x is entirely contained in S;
       * so that (M UNION (M+x)) is a subspace inside S
       */

      fseq new_fseq;

      new_fseq.field_sequence_dimension = dimension;
      new_fseq.field_sequence_length = 2*input_block_size;
      new_fseq.field_sequence_values = malloc(sizeof(vbf_tt_entry) * 2*input_block_size);
      memcpy( new_fseq.field_sequence_values, M, sizeof(vbf_tt_entry) * input_block_size);
      memcpy( new_fseq.field_sequence_values + input_block_size, coset, sizeof(vbf_tt_entry) * input_block_size);
      qsort(new_fseq.field_sequence_values, 2*input_block_size, sizeof(vbf_tt_entry), vbf_tt_compare);

      /* Make sure that the new subset is not already among the computed ones */
      _Bool found = false;
      for(size_t l = 0; l < current_block; ++l) {
	if(!field_sequence_compare( &(*output)[l], &new_fseq)) {
	  found = true;
	  break;
	}
      }

      if(!found) {
	(*output)[current_block++] = new_fseq;

	if(current_block >= TOTAL_SIZE) {
	  TOTAL_SIZE += BLOCK_SIZE;
	  (*output) = realloc((*output), sizeof(fseq) * TOTAL_SIZE);
	}
      }
      else {
	field_sequence_destroy(new_fseq);
      }
    }
  }

  return current_block;
}

fseq vbf_wt_nonbent_signature(vbf_wt WT) {
  size_t counts [WT.vbf_walsh_table_dimension];
  size_t c = 0;
  fseq bf = vbf_wt_bent_components(WT);
  fseq nbf = field_sequence_complement(bf);
  counts[c++] = nbf.field_sequence_length - 1; /* to account for 0 */
  fseq * input;
  fseq * output;
  size_t count = find_2d_subspaces(nbf, &output);
  counts[c++] = count;
  do {
    input = output;
    count = expand_subspaces(nbf, input, count, &output);
    for(size_t i = 0; i < counts[c-1]; ++i) {
      field_sequence_destroy(input[i]);
    }
    free(input);
    counts[c++] = count;
  } while(count);
  for(size_t i = 0; i < count; ++i) {
    field_sequence_destroy(output[i]);
  }
  free(output);

  fseq results; /* this is kind of ugly because we're not returning a sequence of fields elements, but rather of integers */
  results.field_sequence_dimension = 0;
  results.field_sequence_length = c;
  results.field_sequence_values = malloc( sizeof(vbf_tt_entry) * c );
  memcpy(results.field_sequence_values, counts, sizeof(vbf_tt_entry) * c );

  field_sequence_destroy(nbf);
  field_sequence_destroy(bf);

  return results;
}

fseq vbf_tt_image_set(vbf_tt TT) {
  size_t count = 0;
  _Bool hits [TT.vbf_tt_number_of_entries];
  for(size_t x = 0; x < TT.vbf_tt_number_of_entries; ++x) {
    	hits[x] = false;
  }
  for(size_t x = 0; x < TT.vbf_tt_number_of_entries; ++x) {
    size_t y = TT.vbf_tt_values[x];
    if(!hits[y]) {
      ++count;
      hits[y] = true;
    }
  }

  fseq image;
  image.field_sequence_dimension = TT.vbf_tt_dimension;
  image.field_sequence_length = count;
  image.field_sequence_values = malloc( sizeof(vbf_tt_entry) * count );

  size_t j = 0;
  for(size_t x = 0; x < TT.vbf_tt_number_of_entries; ++x) {
    if( hits[x] ) {
      image.field_sequence_values[j++] = x;
    }
  }

  return image;
}


fseq vbf_tt_image_subspaces(vbf_tt TT) {
  size_t counts [TT.vbf_tt_dimension];
  size_t c = 0;
  fseq bf = vbf_tt_image_set(TT);
  counts[c++] = bf.field_sequence_length - 1; /* to account for 0 */
  fseq * input;
  fseq * output;
  size_t count = find_2d_subspaces(bf, &output);
  counts[c++] = count;
  do {
    input = output;
    count = expand_subspaces(bf, input, count, &output);
    for(size_t i = 0; i < counts[c-1]; ++i) {
      field_sequence_destroy(input[i]);
    }
    free(input);
    counts[c++] = count;
  } while(count);
  for(size_t i = 0; i < count; ++i) {
    field_sequence_destroy(output[i]);
  }
  free(output);

  fseq results; /* this is kind of ugly because we're not returning a sequence of fields elements, but rather of integers */
  results.field_sequence_dimension = 0;
  results.field_sequence_length = c;
  results.field_sequence_values = malloc( sizeof(vbf_tt_entry) * c );
  memcpy(results.field_sequence_values, counts, sizeof(vbf_tt_entry) * c );

  field_sequence_destroy(bf);

  return results;
}


fseq vbf_tt_nonbent_signature(vbf_tt TT) {
  size_t counts [TT.vbf_tt_dimension];
  size_t c = 0;
  fseq nbf = vbf_tt_nonbent_components(TT);
  counts[c++] = nbf.field_sequence_length - 1; /* to account for 0 */
  fseq * input;
  fseq * output;
  size_t count = find_2d_subspaces(nbf, &output);
  counts[c++] = count;
  do {
    input = output;
    count = expand_subspaces(nbf, input, count, &output);
    for(size_t i = 0; i < counts[c-1]; ++i) {
      field_sequence_destroy(input[i]);
    }
    free(input);
    counts[c++] = count;
  } while(count);
  for(size_t i = 0; i < count; ++i) {
    field_sequence_destroy(output[i]);
  }
  free(output);

  fseq results; /* this is kind of ugly because we're not returning a sequence of fields elements, but rather of integers */
  results.field_sequence_dimension = 0;
  results.field_sequence_length = c;
  results.field_sequence_values = malloc( sizeof(vbf_tt_entry) * c );
  memcpy(results.field_sequence_values, counts, sizeof(vbf_tt_entry) * c );

  field_sequence_destroy(nbf);

  return results;
}

fseq vbf_tt_pif_single_beta(vbf_tt TT, vbf_tt_entry beta) {
  /* We need to count the number of derivative directions a for which
   * the shifted derivative F(x) + F(a+x) + F(a+beta) maps to b, for every
   * b in the field.
   */

  size_t targets [TT.vbf_tt_number_of_entries]; //counts for all b's
  size_t targetsa [ TT.vbf_tt_number_of_entries+1]; //counts for the current derivative only; +1 for the trick at the end
  //where we count the multiplicities

  for(size_t i = 0; i < TT.vbf_tt_number_of_entries; ++i) {
    targets[i] = 0;
  }

  /* Evaluate every derivative at every point x */
  for(size_t a = 0; a < TT.vbf_tt_number_of_entries; ++a) {
    for(size_t i = 0; i < TT.vbf_tt_number_of_entries; ++i) {
      targetsa[i] = 0;
    }

    for(size_t x = 0; x < TT.vbf_tt_number_of_entries; ++x) {
      size_t b = (TT.vbf_tt_values[x] ^ TT.vbf_tt_values[x^a]) ^ TT.vbf_tt_values[a^beta];
      targetsa[b]++;
    }

    for(size_t i = 0; i < TT.vbf_tt_number_of_entries; ++i) {
      if (targetsa[i]) {
	++targets[i];
      }
    }
  }

  /* We now use the targetsa array to count how many times each multiplicity occurs */
  for(size_t i = 0; i <= TT.vbf_tt_number_of_entries; ++i) {
    targetsa[i] = 0;
  }

  for(size_t i = 0; i < TT.vbf_tt_number_of_entries; ++i) {
    targetsa[ targets[i] ]++;
  }

  /* Sort the array of multiplicities */
  qsort(targetsa, TT.vbf_tt_number_of_entries+1, sizeof(vbf_tt_entry), compare_size_t);

  size_t i = 0;
  for( ; !targetsa[i]; ++i);

  fseq results;
  results.field_sequence_dimension = TT.vbf_tt_dimension;
  results.field_sequence_length = TT.vbf_tt_number_of_entries+1-i;
  results.field_sequence_values = malloc( sizeof(vbf_tt_entry) * (TT.vbf_tt_number_of_entries) );

  for(size_t j = i ; j <= TT.vbf_tt_number_of_entries; ++j) {
      results.field_sequence_values[j-i] = targetsa[j];
  }

  return results;
}


/* fINITE FIELD MULTIPLICATION */

/* Library of primitive polynomials */
vbf_tt_entry vbf_tt_get_primitive_polynomial(size_t dimension) {
  assert( dimension >= 2 );
  assert( dimension <= 50 );

 vbf_tt_entry pps [] = { 7, 11, 19, 37, 91, 131, 285, 529, 1135, 2053, 4331, 8219, 16553, 32821, 65581, 131081, 267267, 524327, 1050355, 2097253, 4202337, 8388641, 16901801, 33554757, 67126739, 134223533, 268443877, 536870917, 1073948847, 2147483657, 4295000729, 8589950281, 17179974135, 34359741605, 68733788515, 137438953535, 274877925159, 549755854565, 1099522486571, 2199023255561, 4399239010919, 8796093022297, 17592203542555, 35184373323841, 70368755859457, 140737488355361, 281475018792329, 562949953422687, 1125900847118165 };

 return pps[dimension-2]; //since listing begins at n = 2
}

vbf_tt_entry vbf_tt_ff_multiply(vbf_tt_entry a, vbf_tt_entry b, vbf_tt_entry pp, size_t dimension) {
  vbf_tt_entry result = 0;

  /* The value at which we should reduce the numbers using the primitive polynomial */
  size_t cutoff = 1;
  for (size_t i = 0; i < dimension-1; ++i) {
    cutoff <<= 1;
  }

  while(a && b) {
    if (b & 1) { /* if b is odd, add a to the total */
      result ^= a;
    }

    if (a & cutoff) {
      a = (a << 1) ^ pp; /* reduce */
    }
    else {
      a <<= 1;
    }

    b >>= 1;
  }

  return result;
}

vbf_tt_entry vbf_tt_exponentiate(vbf_tt_entry a, size_t exponent, vbf_tt_entry pp, size_t dimension) {
  if(!exponent) {
    return 1;
  }

  vbf_tt_entry total = a;

  /* Initialize a bit selector mask to point to the highest order bit of the exponent */
  size_t bit_selector = 1;
  while(bit_selector <= exponent) {
    bit_selector <<= 1;
  }
  bit_selector >>= 2; /* shift by two to ignore the first bit (which is always 1) */
  while(bit_selector) {
    /* Square */
    total = vbf_tt_ff_multiply(total,total,pp,dimension);
    /* Multiply */
    if(exponent & bit_selector) {
      total = vbf_tt_ff_multiply(total,a,pp,dimension);
    }
    /* Shift */
    bit_selector >>= 1;
  }

  return total;
}

/* UNIVARIATE POLYNOMIALS */
void unipol_print(unipol u) {
  for(size_t i = 0; i < u.univariate_polynomial_number_of_terms-1; ++i) { /* -1 so we don't add a plus after the last term */
    printf("[%lu]^%lu + ", u.univariate_polynomial_coefficients[i], u.univariate_polynomial_exponents[i]);
  }
  printf("[%lu]^%lu\n", u.univariate_polynomial_coefficients[u.univariate_polynomial_number_of_terms-1], u.univariate_polynomial_exponents[u.univariate_polynomial_number_of_terms-1]);
}

void unipol_destroy(unipol u) {
  free(u.univariate_polynomial_coefficients);
  free(u.univariate_polynomial_exponents);
}

vbf_tt unipol_to_tt(unipol u, vbf_tt_entry primitive_polynomial) {
  size_t dimension = u.univariate_polynomial_dimension;

  vbf_tt result;
  result.vbf_tt_dimension = dimension;
  result.vbf_tt_number_of_entries = DIM2SIZE(dimension);
  result.vbf_tt_values = malloc( sizeof(vbf_tt_entry) * result.vbf_tt_number_of_entries );

  /* Prepare a table with exponents of all finite field elements; EXP[i][x] will contain x^e for e = u.univariate_polynomial_exponents[i] */
  vbf_tt_entry EXP[u.univariate_polynomial_number_of_terms][result.vbf_tt_number_of_entries];
  for(size_t x = 0; x < result.vbf_tt_number_of_entries; ++x) {
    for(size_t i = 0; i < u.univariate_polynomial_number_of_terms; ++i) {
      EXP[i][x] = vbf_tt_exponentiate(x,u.univariate_polynomial_exponents[i],primitive_polynomial,dimension);
    }
  }

  for(size_t x = 0; x < result.vbf_tt_number_of_entries; ++x) {
    vbf_tt_entry evaluation = 0;
    for(size_t i = 0; i < u.univariate_polynomial_number_of_terms; ++i) {
      evaluation ^= vbf_tt_ff_multiply(EXP[i][x], u.univariate_polynomial_coefficients[i], primitive_polynomial, dimension);
    }
    result.vbf_tt_values[x] = evaluation;
  }
  
  return result;
}

vbf_tt power_to_tt(size_t exp, size_t n) {
  vbf_tt tt;
  tt.vbf_tt_dimension = n;
  tt.vbf_tt_number_of_entries = (1L << n);
  tt.vbf_tt_values = malloc( sizeof(vbf_tt_entry) * tt.vbf_tt_number_of_entries );

  vbf_tt_entry pp = vbf_tt_get_primitive_polynomial(n);

  for(size_t x = 0; x < tt.vbf_tt_number_of_entries; ++x) {
    tt.vbf_tt_values[x] = vbf_tt_exponentiate(x, exp, pp, n);
  }

  return tt;
}

_Bool vbf_tt_is_3_to_1(vbf_tt F) {
  size_t entries = DIM2SIZE(F.vbf_tt_dimension);
  unsigned short counters [ entries ];
  for(size_t i = 0; i < entries; ++i) {
    counters[i] = 0;
  }

  for(size_t x = 0; x < entries; ++x) {
    if(++counters[F.vbf_tt_values[x]] > 3) {
      return false;
    }
  }

  /* Count the number of images */
  size_t count = 0;
  for(size_t x = 0; x < entries; ++x) {
    count += counters[x] ? 1 : 0;
  }
  size_t target_value = ((entries - 1) / 3) + 1;
  return (count == target_value);
}

void vbf_tt_differential_spectrum(vbf_tt f) {
	/* This will count the number of times each multiplicity is hit */
	size_t * counts = calloc( f.vbf_tt_number_of_entries, sizeof(size_t) );
	/* This will count the number of different values in F(x) + F(a+x) for a fixed a */
	size_t * solutions = malloc( sizeof(size_t) * f.vbf_tt_number_of_entries );

	for(size_t a = 1; a < f.vbf_tt_number_of_entries; ++a) {
		for(size_t x = 0; x < f.vbf_tt_number_of_entries; ++x) {
			solutions[x] = 0;
		}

		for(size_t x = 0; x < f.vbf_tt_number_of_entries; ++x) {
			vbf_tt_entry hit = f.vbf_tt_values[x] ^ f.vbf_tt_values[a^x];
			++solutions[hit];
		}

		for(size_t c = 0; c < f.vbf_tt_number_of_entries; ++c) {
			++counts[ solutions[c] ];
		}
	}

	for(size_t c = 0; c < f.vbf_tt_number_of_entries; ++c) {
		if(counts[c]) {
			printf("%lu^^%lu, ", c, counts[c]);
		}
	}
	printf("\n");

	free(solutions);
	free(counts);
}

void vbf_tt_extended_walsh_spectrum(vbf_tt f) {
	/* All elements of the extended Walsh spectrum are non-negative, and upper bounded by 2^n, so
	 * we can proceed like in vbf_tt_differential_spectrum and have an array of counters */
	size_t * counts = calloc( f.vbf_tt_number_of_entries, sizeof(size_t) );

	for(size_t a = 0; a < f.vbf_tt_number_of_entries; ++a) {
		for(size_t b = 1; b < f.vbf_tt_number_of_entries; ++b) {
			long wc = vbf_tt_walsh_transform(f,a,b);
			size_t absolute_value = (wc >= 0) ? wc : (-wc);
			++counts[absolute_value];
		}
	}

	for(size_t c = 0; c < f.vbf_tt_number_of_entries; ++c) {
		if(counts[c]) {
			printf("%lu^^%lu, ", c, counts[c]);
		}
	}
	printf("\n");

	free(counts);
}

/* map_size : size (number of size_t's) of map_A and map_B and map_choices
 * image_size : number of basis elements already assigned an image
 * n : dimension
 * map_A, map_B : Boolean maps giving which elements are in A and which are in B
 * map_choices : possible choices for the next basis image
 * BASIS_IMAGES : already assigned images
 */
vbf_tt aux_are_sets_linear_equivalent(size_t map_size, size_t image_size, size_t n, size_t * map_A, size_t * map_B, size_t * map_choices, size_t * BASIS_IMAGES) {
  vbf_tt result;
  result.vbf_tt_values = 0;

  if(image_size == n) {
    /* Reconstruct truth table and return */
    result.vbf_tt_dimension = n;
    result.vbf_tt_number_of_entries = (1L << n);
    result.vbf_tt_values = malloc( sizeof(size_t) * result.vbf_tt_number_of_entries );
    for(size_t x = 0; x < (1L << n); ++x) {
      size_t y = 0;
      for(size_t j = 0; j < n; ++j) {
	if(x & (1L << j)) {
	  y ^= BASIS_IMAGES[j];
	}
      }

      result.vbf_tt_values[x] = y;
    }

    return result;
  }

  /* Guess next image */
  size_t b = (1L << image_size);
  for(size_t y = 0; y < (1L << n); ++y) {
    if(!get_bit(map_choices,y)) {
      continue;
    }

    /* Assigning b -> y, check whether some of the newly generated images do not violate A -> B */
    _Bool problem = false;

    for(size_t g = 0; g < (1L << image_size); ++g) {
      size_t new_y = y;
      for(size_t j = 0; j < image_size; ++j) {
	if( (1L << j) & g ) {
	  new_y ^= BASIS_IMAGES[j];
	}
      }

      if( (get_bit(map_A, b^g) && !get_bit(map_B,new_y)) || (!get_bit(map_A, b^g) && get_bit(map_B,new_y)) ) {
	problem = true;
	break;
      }
    }

    if(!problem) {
      /* Go to next basis element */
      BASIS_IMAGES[image_size] = y;
      
      /* Update choices */
      for(size_t g = 0; g < (1L << image_size); ++g) {
	size_t new_y = y;
	for(size_t j = 0; j < image_size; ++j) {
	  if( (1L << j) & g ) {
	    new_y ^= BASIS_IMAGES[j];
	  }
	}
	set_bit(map_choices, new_y, false);
      }

      result = aux_are_sets_linear_equivalent(map_size, image_size+1, n, map_A, map_B, map_choices, BASIS_IMAGES);
      if(result.vbf_tt_values) {
	return result;
      }

      /* Unset choices */
      for(size_t g = 0; g < (1L << image_size); ++g) {
	size_t new_y = y;
	for(size_t j = 0; j < image_size; ++j) {
	  if( (1L << j) & g ) {
	    new_y ^= BASIS_IMAGES[j];
	  }
	}
	set_bit(map_choices, new_y, true);
      }
    }
  }

  return result;
}

vbf_tt are_sets_linear_equivalent(fseq A, fseq B) {
  assert (A.field_sequence_dimension == B.field_sequence_dimension);
  assert (A.field_sequence_length == B.field_sequence_length);
  size_t n = A.field_sequence_dimension;
  size_t K = A.field_sequence_length;

  /* Make maps for A and B, and for the possible choices */
  size_t map_size = (1L << n) / sizeof(size_t);
  if( sizeof(size_t) * map_size < (1L << n) ) {
    ++map_size;
  }

  size_t map_A [map_size];
  size_t map_B [map_size];
  size_t map_choices [map_size];


  for(size_t i = 0; i < map_size; ++i) {
    map_A[i] = 0;
    map_B[i] = 0;
    map_choices[i] = ~0;
  }
  set_bit(map_choices, 0, false);

  for(size_t i = 0; i < K; ++i) {
    set_bit(map_A, A.field_sequence_values[i], true);
    set_bit(map_B, B.field_sequence_values[i], true);
  }

  size_t BASIS_IMAGES [n];

  vbf_tt result = aux_are_sets_linear_equivalent(map_size, 0, n, map_A, map_B, map_choices, BASIS_IMAGES);
  return result;
}

/* Guesses the next image of a basis element */
/* If all = false, returns as soon as one instance of l is found */
vbf_tt * aux_guess_basis_image(vbf_wt WT, size_t * basis_images, size_t i, _Bool all) {
  /* If all basis elements have an image, reconstruct TT and return */
  if (i == WT.vbf_walsh_table_dimension) {
    vbf_tt * result = malloc( sizeof(vbf_tt) );
    result->vbf_tt_dimension = WT.vbf_walsh_table_dimension;
    result->vbf_tt_number_of_entries = (1L << result->vbf_tt_dimension);
    result->vbf_tt_values = malloc( sizeof(vbf_tt_entry) * result->vbf_tt_number_of_entries );

    for(size_t x = 0; x < result->vbf_tt_number_of_entries; ++x) {
      size_t y = 0;
      size_t mask = 1;
      for(size_t j = 0; j < result->vbf_tt_dimension; ++j) {
	if (mask & x) {
	  y ^= basis_images[j];
	}
	mask <<= 1;
      }
      result->vbf_tt_values[x] = y;
    }

    return result;
  }

  /* The basis consists of the elements 1, 1 << 1, 1 << 2, etc. up to 1 << n-1 */
  /* Guess the next element; if L*(b) = y, then W_F(y,b) mod 3 = 1 */

  size_t b = (1L << i); /* basis element whose image we guess */

  for(size_t y = 0; y < (1L << WT.vbf_walsh_table_dimension); ++y) {
    int mod = WT.vbf_walsh_table_values[y][b] % 3;
    mod = (mod >= 0) ? mod : mod + 3;
    if( mod != 1) {
      continue;
    }

    /* We still need to check whether all elements generated by the new image
     * satisfy the necessary condition with the mod 3
     */
    _Bool problem = false;
    for(size_t d = 0; i > 0 && d < (1L << (i-1)); ++d) {
      size_t new_x = b ^ d;
      size_t new_y = y;
      for(size_t j = 0; i > 0 && j < i-1; ++j) {
	if( (1L << j) & d) {
	  new_y ^= basis_images[j];
	}
      }
      mod = (WT.vbf_walsh_table_values[new_y][new_x] % 3);
      mod = (mod >= 0) ? mod : mod + 3;
      if( mod != 1) {
	problem = true;
	break;
      }
    }
    if (!problem) {
      basis_images[i] = y;
      vbf_tt * potential_result = aux_guess_basis_image(WT, basis_images, i+1, all);
      if (potential_result) {
        /* If we need to output just one linear l, we return it now; otherwise,
	 * we merely print it, and keep going */
      	if(!all) {
		return potential_result;
	}
	else {
		for(size_t x = 0; x < potential_result->vbf_tt_number_of_entries; ++x) {
			printf("%lu ", potential_result->vbf_tt_values[x]);
		}
	}
      }
    }
  }

  return 0;
}

vbf_tt * vbf_tt_is_equivalent_to_triplicate(vbf_tt f) {
  vbf_wt WT = vbf_tt_to_wt(f);
  size_t n = f.vbf_tt_dimension;
  
  /* The basis will consist of the elements 1, 1 << 1, 1 << 2, etc. up to 1 << n-1 */
  size_t * basis_images = malloc( sizeof(size_t) * n );

  return aux_guess_basis_image(WT, basis_images, 0, false);
}

void vbf_tt_is_equivalent_to_triplicate_all(vbf_tt f) {
  vbf_wt WT = vbf_tt_to_wt(f);
  size_t n = f.vbf_tt_dimension;
  size_t * basis_images = malloc( sizeof(size_t) * n );
  aux_guess_basis_image(WT, basis_images, 0, true);
}

