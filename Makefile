all: alg1 alg2 alg3 alg4 alg_e1 alg_e2 alg_e3

alg1: alg1.c vbf.c
	gcc alg1.c vbf.c -lm -o check_lin_eq_2x_uniform_3to1.o

alg2: alg2.c vbf.c
	gcc alg2.c vbf.c -lm -o find_uniform_3to1_lin_eq_to_3to1.o

alg3: alg3.c vbf.c
	gcc alg3.c vbf.c -lm -o find_3to1_add_eq_to_f.o

alg4: alg4.c vbf.c
	gcc alg4.c vbf.c -lm -o find_3to1_add_eq_to_f_faster.o

alg_e1: alg_e1.c vbf.c
	gcc alg_e1.c vbf.c -lm -o lin_eq_to_self.o

alg_e2: alg_e2.c vbf.c
	gcc alg_e2.c vbf.c -lm -o check_add_eq_to_triplicate.o

alg_e3: alg_e3.c vbf.c
	gcc alg_e3.c vbf.c -lm -o partition_by_L2.o

