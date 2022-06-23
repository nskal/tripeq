#ifndef VBF_H
#define VBF_H 1

#include <stdbool.h>

#define DIM2SIZE(D) ( 1L << D )
#define POPCOUNT_FUNCTION __builtin_popcountl

typedef unsigned long vbf_tt_entry;
typedef long vbf_walsh_table_entry;

typedef struct vbf_truth_table vbf_tt;
typedef struct vbf_walsh_table vbf_wt;

struct vbf_truth_table {
	size_t vbf_tt_dimension;
	size_t vbf_tt_number_of_entries;
	vbf_tt_entry * vbf_tt_values;
};

/* A "field sequence" is used to return a collection of field elements from functions */
typedef struct field_sequence fseq;

struct field_sequence {
	size_t field_sequence_dimension;
	size_t field_sequence_length;
	vbf_tt_entry * field_sequence_values;
};

fseq field_sequence_complement(fseq fs);

/* We compare two sequences as follows:
 * 1)If the length are different, the shorter one is "less";
 * 2)If the lengths are the same, and A[1] < B[1], then A < B;
 * 3)If A[1] = B[1] but A[2] < B[2], then A < B;
 * 4)...
 * 5)If A[i] = B[i] for all i, then A = B
 */
int field_sequence_compare(const void * a, const void * b);

void field_sequence_destroy(fseq fs);

/* Shifts all elements of a given sequence by a given constant */
void field_sequence_add_constant(fseq fs, size_t c);

struct vbf_walsh_table {
  size_t vbf_walsh_table_dimension;
  vbf_walsh_table_entry ** vbf_walsh_table_values;
};

/* Frees space */
void vbf_tt_destroy(vbf_tt tt);
void vbf_wt_destroy(vbf_wt tt);

/* Loads a truth table from a file, given in the format:
 * - dimension on the first line
 * - integers in the range [0..2^dimension-1] separated by spaces on the second line
 */
vbf_tt load_vbf_tt_from_file(char const path[static 1]);

void vbf_tt_print_truth_table(vbf_tt tt);

/* Makes completely new copy (memcpy to newly allocated partition) */
vbf_tt vbf_tt_copy(vbf_tt src);

/* Composition of two functions given as truth tables; we get dest[x] = dest[src[x]] for all x */
void vbf_tt_compose(vbf_tt * dest, vbf_tt * src);

/* Multiplies all entries in a truth table by a constant, i.e. given the truth table of F,
 * computes the truth table of c*F. Computation in place.
 */
void vbf_tt_multiply_by_constant(vbf_tt tt, vbf_tt_entry c);

/* Addition of truth tables */
void vbf_tt_add(vbf_tt to, vbf_tt from);

/* INVARIANTS */

/* Computation of the bent components of a given VBF from its Walsh table */
fseq vbf_wt_bent_components(vbf_wt WT);

/* Direct computation of bent component (may be faster if no Walsh table is available) */
fseq vbf_tt_nonbent_components(vbf_tt TT);

/* Smallest basis (in lexicographic order) generating a given subspace
 * NB: WE ASSUME THAT THE GIVEN SET OF ELEMENTS IS A SUBSPACE AND IS *SORTED*;
 * this is used to designate a "canonical" basis among all possible bases of a
 * given set and to ignore duplicates when counting the number of sets
 */
fseq smallest_basis(fseq subspace);

/* Compute list of all 2-dimensional linear subspaces contained in a given set */
size_t find_2d_subspaces(fseq S, fseq ** output);

/* Expand k-dimensional subspaces to (k+1)-dimenional subspaces inside a set */
size_t expand_subspaces(fseq S, fseq * input, size_t input_size, fseq ** output);

/* Gologlu's nonbent signature */
fseq vbf_wt_nonbent_signature(vbf_wt WT);

/* Same, but without using the Walsh transform (may be faster if we don't have
 * a precomputed Walsh table
 */
fseq vbf_tt_nonbent_signature(vbf_tt TT);

/* The PI_F(beta) multiset for a fixed value of beta */
fseq vbf_tt_pif_single_beta(vbf_tt TT, vbf_tt_entry beta);

/* Sequence of elements in the image set of a given function (no multiplicities) */
fseq vbf_tt_image_set(vbf_tt TT);

/* Number of subspaces in image set (linear-equivalence invariant, same format as vbf_tt_nonbent_signature) */
fseq vbf_tt_image_subspaces(vbf_tt TT);


/* WALSH TRANSFORM */

/* Dot product of two field elements, computed by summing the products of all corresponding pairs */
_Bool dot(vbf_tt_entry a, vbf_tt_entry b);

/* Walsh transform of F given via TT at given (a,b) */
long vbf_tt_walsh_transform(vbf_tt TT, vbf_tt_entry a, vbf_tt_entry b);

/* Convert truth table to Walsh table */
vbf_wt vbf_tt_to_wt(vbf_tt tt);

/* Power moments of the Walsh transform; the power moment computed is of the form
 * 	SUM_{a,b in F} chi(a*shift_a) * chi(b*shift_b) * W_F(a,b)^k;
 * thus, the "classical" power moments have shift_a = shift_b = 0.
 */
long vbf_wt_power_moment(vbf_wt WT, short unsigned k, vbf_tt_entry shift_a, vbf_tt_entry shift_b);

void vbf_wt_print_walsh_table(vbf_wt wt);

/* Partition of finite field according to multiplicities of shifted power moments for the EA-equivalence algorithm */

typedef struct partition partition;

struct partition {
  size_t partition_dimension;
  short unsigned partition_number_of_classes;
  size_t * partition_class_sizes;
  vbf_tt_entry ** partition_classes;
};

void ea_partition_print(partition p);

void ea_partition_destroy(partition p);

/* Partition elements directly from the definition, for k = 4 */
void ea_partition_4(vbf_tt TT);

/* Partition elements according to the values of the k-th power moment shifted by (0,a) */
partition ea_partition_walsh(vbf_wt WT, short unsigned k);

/* Find a maximal linearly independent subset with a given set (of elements in a finite field) */
fseq findMaximalLinearlyIndependentSubset(fseq subset);

/* Find all linear functions preserving a given set of partitions; this uses the standard basis 000...1, 000...10, ..., 100...0, which faciliates implementation in C; each function is represented by its images of the standard basis; the number of functions found is returned; memory is allocated to the given pointer, and the actual basis
 * images are written there*/
size_t ea_find_outer_permutations_preserving_partition(partition p, fseq ** output);

/* Compute the sets O_F^3(t) of all elements x belonging to triples (x,y,x+y) mapping to t under F; the results are written in a 2d Boolean array,
 * such that output[x][y] = true iff y belongs to O^f_3(x) */
void ea_find_union_of3t(vbf_tt f, _Bool *** output);

/* Compute the domain of L(x) for one given variable x for F * L + A = G */
fseq ea_compute_domain(vbf_tt f, vbf_tt g, _Bool ** of3t_table, vbf_tt_entry x);

/* Returns the standard basis for the given dimension */
fseq ea_get_standard_basis(size_t dimension);

/* Returns a sequence of elements M such that M[x] = y if x and y have the same coordinates w.r.t. the standard basis and the given basis, respectively */
fseq ea_get_basis_map(fseq basis);

/* Given a basis and a set of domains for the basis, attempts to reconstruct the inner permutation L2 such that F * L2 + L = G for L linear; returns the first set of basis images for which F * L2 + G is a linear function */
fseq ea_find_inner_permutation(vbf_tt f, vbf_tt g, fseq basis, fseq * domains);

/* Ortho-derivatives */
vbf_tt tt_orthoderivative(vbf_tt f);

/* For testing purposes */
vbf_tt random_linear_permutation(size_t dimension);
vbf_tt random_linear_function(size_t dimension);
fseq random_linear_subspace(size_t dimension, size_t subspace_dimension); 

_Bool vbf_tt_is_linear(vbf_tt f);
_Bool vbf_tt_is_permutation(vbf_tt f);

/* Finite field multiplication */
vbf_tt_entry vbf_tt_get_primitive_polynomial(size_t dimension); /* library of primitive polynomials for dimensions up to 50 */
vbf_tt_entry vbf_tt_ff_multiply(vbf_tt_entry a, vbf_tt_entry b, vbf_tt_entry pp, size_t dimension); /* multiplication of two field elements */
vbf_tt_entry vbf_tt_exponentiate(vbf_tt_entry a, size_t exponent, vbf_tt_entry pp, size_t dimension); /* square and multiply */

/* Univariate polynomials over finite fields */
typedef struct univariate_polynomial unipol;

struct univariate_polynomial {
  size_t univariate_polynomial_dimension;
  size_t univariate_polynomial_number_of_terms;
  vbf_tt_entry * univariate_polynomial_coefficients;
  size_t * univariate_polynomial_exponents;
};

void unipol_print(unipol u);

void unipol_destroy(unipol u);

/* Creates a truth table for a function represented by a univariate polynomial */
vbf_tt unipol_to_tt(unipol u, vbf_tt_entry primitive_polynomial);

/* Creates a truth-table for the  power function x^exp over GF(2^n) */
vbf_tt power_to_tt(size_t exp, size_t n);

/* Cryptographic properties and such */

_Bool vbf_tt_is_3_to_1(vbf_tt F);

/* Prints the differential spectrum in the format ELEMENT^^MULTIPLICITY */
void vbf_tt_differential_spectrum(vbf_tt f);

/* Prints the extended Walsh spectrum in the format ELEMENT^^MULTIPLICITY */
void vbf_tt_extended_walsh_spectrum(vbf_tt f);

/* UTILITIES */

/* Checks whether there exists a linear permutation L mapping A to B. Returns L, or an empty
 * struct if no such L exists.
 */
vbf_tt are_sets_linear_equivalent(fseq A, fseq B);

/* TRIPLICATE FUNCTIONS */
/* If the given function f can be written as f = g + l for a triplicate function g and
 * a linear function l, returns the truth table of the adjoint of l (with respect to the
 * standard scalar product, as implemented in dot(). Otherwise, returns 0.
 */
vbf_tt * vbf_tt_is_equivalent_to_triplicate(vbf_tt f);

/* Same as above, but prints all linear l satisfying for which + f is triplicate */
void vbf_tt_is_equivalent_to_triplicate_all(vbf_tt f);


#endif
