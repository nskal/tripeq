#include <stdio.h>
#include "vbf.h"

/* Check whether a given function is EA-equivalent to a triplicate function */
/* Returns trurth table of the adjoint L such that F + L = G, or prints "False" */
int main(int argc, char ** argv) {
	if(argc != 2) {
		printf("Usage: %s TT_FILE\n", argv[0]);
		return 1;
	}

	vbf_tt f = load_vbf_tt_from_file(argv[1]);

	vbf_tt * result = vbf_tt_is_equivalent_to_triplicate(f);
	if(result) {
	  for(size_t x = 0; x < result->vbf_tt_number_of_entries; ++x) {
	    printf("%lu ", result->vbf_tt_values[x]);
	  }
	  printf("\n");
	  vbf_tt_destroy(*result);
	}
	else {
	  printf("False\n");
	}

	vbf_tt_destroy(f);

	return 0;
}
