## Algorithm implementation

All algorithms presented below work with functions implemented as truth tables.
Truth table file consists of two lines. First line has one number denoting dimension, second line has 2^dimension numbers denoting function images.
Example truth table of Gold function (x^3) in dimension 6 can be found in file `example_function.tt`.

Contributors:
- Ivana Ivkovic
- Nikolay Stoyanov Kaleyski 

### Library
vbf.h - vectorial boolean function library header

vbf.c - vectorial boolean function library

latest implementation maintained at:
[VBF GitLab](https://git.app.uib.no/Nikolay.Kaleyski/vectorial-boolean-functions)

---

### Algorithm 1: Testing linear equivalence of two uniformly distributed functions
_Check whether two uniformly distributed 3-to-1 functions (C1 and C2) are linear-equivalents_

alg1.c

**to compile:**

`make alg1`

**or:**

`gcc alg1.c vbf.c -lm -o check_lin_eq_2x_uniform_3to1.o`

**to run:**

`./check_lin_eq_2x_uniform_3to1.o function1.tt function2.tt`

**result:**

Truth tables of the linear functions L1 and L2 such that L1 ◦ C1 ◦ L2 = C2

**or:**

"False"

---

### Algorithm 2: Testing linear equivalence of a 3-to-1 function to a uniformly distributed 3-to-1 function
_Check whether a given function (T) is linear-equivalent to a uniformly distributed 3-to-1 function (C)_

alg2.c

**to compile:**

`make alg2`

**or:**

`gcc alg2.c vbf.c -lm -o find_uniform_3to1_lin_eq_to_3to1.o`

**to run:**

`./find_uniform_3to1_lin_eq_to_3to1.o function.tt`

**result:**

Truth table of the uniformly distributed 3-to-1 function C such that T ◦ L = C where L is a linear function. 
_*It is possible to modify the code to return the truth table of L._


**or:**

"False"

---

### Algorithm 3: Testing additive-equivalence to a quadratic 3-to-1 function with the zero-sum property
_Check whether a given function F is additive-equivalent to a quadratic 3-to-1 function T with zero-sum property_

alg3.c

**to compile:**

`make alg3`

**or:**

`gcc alg3.c vbf.c -lm -o find_3to1_add_eq_to_f.o`

**to run:**

`./find_3to1_add_eq_to_f.o function.tt`

**result:**

truth table of the 3-to-1 function T such that F + A = T

**or:**

"False"

---

### Algorithm 4: Testing additive equivalence to a quadratic 3-to-1 function with the zero-sum and pre-image summation properties
_Check whether a given function F is additive-equivalent to a quadratic 3-to-1 function T with zero-sum and pre-image summation properties_

alg4.c

**to compile:**

`make alg4`

**or:**

`gcc alg4.c vbf.c -lm -o find_3to1_add_eq_to_f_faster.o`

**to run:**

`./find_3to1_add_eq_to_f_faster.o function.tt`

**result:**

truth table of the 3-to-1 function T such that F + A = T

**or:**

"False"

---


## Extra Algorithms

### Algorithm E1: Finding linear self-equivalence classes of a uniformly distributed 3-to-1 function
_Find all linear functions L1 and L2 for which a given uniformly distributed 3-to-1 function is linearly equivalent to self_

alg_e1.c

**to compile:**

`make alg_e1`

**or:**

`gcc alg_e1.c vbf.c -lm -o lin_eq_to_self.o`

**to run:**

`./lin_eq_to_self.o function.tt`

**result:**

truth tables of all the linear functions L1 and L2 such that L1 ◦ C1 ◦ L2 = C1

---

### Algorithm E2: Testing additive equivalence to a triplicate function
_Check whether a given function F is additive-equivalent to a triplicate function T (not necessarily 3-to-1)_

alg_e2.c

**to compile:**

`make alg_e2`

**or:**

`gcc alg_e2.c vbf.c -lm -o check_add_eq_to_triplicate.o`

**to run:**

`./check_add_eq_to_triplicate.o function.tt`

**result:**

truth table of the adjoint L such that F + L = G

**or:**

"False"

### Algorithm E3: Finding the orbits partition for L2
_Partition the domain of F into right orbits using L2 from self-equivalence classes_

alg_e3.c

**to compile:**

`make alg_e3`

**or:**

`gcc alg_e3.c vbf.c -lm -o partition_by_L2.o`

**to run:**

`./partition_by_L2.o function.tt`

**result:**

Partition into right orbits. Numbers denote the corresponding orbit, while positions of numbers denote the pre-images of F. 
