#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <bigint.h>

#define NTESTS 50000

char filename[] = "regression_tests.dat";

/* Error formatting */
void matherr(bigint in1, bigint in2, bigint exp, bigint out,
	     char *msg);
void sqrterr(bigint in, bigint exp, bigint out, char *msg);

/* Timing tests */
clock_t test(int size, char *name, bigint l[], bigint r[],
          bigint (*bigint_op)(bigint l, bigint r), bigint op[]);
clock_t test_negate(int size, bigint l[], bigint op[]);
clock_t test_cmp(int size, bigint l[], bigint r[], int op[]);
clock_t test_division(int size, bigint l[], bigint r[], bigint op[]);
clock_t test_sqrt(int size, bigint l[], bigint op[]);

int main(void) {
  static bigint a[NTESTS], b[NTESTS];
  static bigint add[NTESTS], sub[NTESTS], mul[NTESTS];
  static bigint sqrt[NTESTS], div[NTESTS], neg[NTESTS];
  static int comp[NTESTS];
  int N, nmemb;
  clock_t total = 0;

  FILE *inf = fopen(filename, "r");
  if (inf == NULL) {
    perror("Failed to open file");
    exit(2);
  }

  N = 0;
  do {
    a[N] = bigint_read_binary(inf);
    b[N] = bigint_read_binary(inf);
    add[N] = bigint_read_binary(inf);
    sub[N] = bigint_read_binary(inf);
    mul[N] = bigint_read_binary(inf);
    sqrt[N] = bigint_read_binary(inf);
    div[N] = bigint_read_binary(inf);
    neg[N] = bigint_read_binary(inf);

    nmemb = fread(comp+N, sizeof(int), 1, inf);
    if(nmemb != 1) {
      perror("Unable to read from file");
      exit(100);
    }

    N++;
  } while ((N < NTESTS) && (a[N-1] != NULL) && (b[N-1] != NULL) &&
            (add[N-1] != NULL) && (sub[N-1] != NULL) &&
            (mul[N-1] != NULL) && (div[N-1] != NULL));

  fclose(inf);

  // Run tests
  total += test_negate(N, a, neg);
  total += test_cmp(N, a, b, comp);
  total += test(N, "Add", a, b, bigint_add, add);
  total += test(N, "Sub", a, b, bigint_sub, sub);
  total += test(N, "Mul", a, b, bigint_mul, mul);
  total += test_division(N, a, b, div);
  total += test_sqrt(N, a, sqrt);

  // Total time
  printf("Total time :\t %lf\n",(total)/(double)CLOCKS_PER_SEC);

  // Free
  for(int i = 0; i < N; i++) {
    bigint_free(a[i]);
    bigint_free(b[i]);
    bigint_free(add[i]);
    bigint_free(sub[i]);
    bigint_free(mul[i]);
    bigint_free(sqrt[i]);
    bigint_free(div[i]);
    bigint_free(neg[i]);
  }

  return 0;
}

void matherr(bigint in1, bigint in2, bigint exp, bigint out, char *msg) {
  char *input1, *input2, *expected, *actual;
  input1 = bigint_to_str(in1);
  input2 = bigint_to_str(in2);
  expected = bigint_to_str(exp);
  actual = bigint_to_str(out);
  printf("Error in %s:\ninputs:\n%s\n%s\n", msg, input1, input2);
  printf("correct output: %s\n", expected);
  printf("output: %s\n", actual);
  exit(4);
}

void sqrterr(bigint in, bigint exp, bigint out, char *msg) {
  char *input, *expected, *actual;
  input = bigint_to_str(in);
  expected = bigint_to_str(exp);
  actual = bigint_to_str(out);
  printf("Error in %s:\ninput: %s\n", msg, input);
  printf("correct output: %s\n", expected);
  printf("output: %s\n", actual);
  exit(4);
}

clock_t test(int size, char *name, bigint l[], bigint r[],
          bigint (*bigint_op)(bigint l, bigint r), bigint op[]) {
  bigint d;
  clock_t stop, start = clock();
  for (int i = 0; i < size; i++) {
    d = bigint_op(l[i], r[i]);
    if (bigint_ne(d, op[i]))
      matherr(l[i], r[i], op[i], d, name);
    bigint_free(d);
  }
  stop = clock();
  printf("%s :\t %lf\n", name, (stop - start)/(double)CLOCKS_PER_SEC);
  return (stop - start);
}

clock_t test_negate(int size, bigint l[], bigint op[]) {
  char *name = "Neg";
  bigint d;
  clock_t stop, start = clock();
  for (int i = 0; i < size; i++) {
    d = bigint_negate(l[i]);
    if (bigint_ne(d, op[i]))
      matherr(l[i], l[i], op[i], d, name);
    bigint_free(d);
  }
  stop = clock();
  printf("%s :\t %lf\n", name, (stop - start)/(double)CLOCKS_PER_SEC);
  return (stop - start);
}

clock_t test_cmp(int size, bigint l[], bigint r[], int op[]) {
  char *name = "Cmp";
  int d;
  clock_t stop, start = clock();
  bigint expected, actual;
  for (int i = 0; i < size; i++) {
    d = bigint_cmp(l[i], r[i]);
    if (d != op[i]) {
      actual = bigint_from_int(d);
      expected = bigint_from_int(op[i]);
      matherr(l[i], r[i], expected, actual, name);
    }
  }
  stop = clock();
  printf("%s :\t %lf\n", name, (stop - start)/(double)CLOCKS_PER_SEC);
  return (stop - start);
}

clock_t test_division(int size, bigint l[], bigint r[], bigint op[]) {
  char *name = "Div";
  bigint d, labs, rabs;
  clock_t stop, start = clock();
  for (int i = 0; i < size; i++) {
    /* Use largest absolute value for dividend and smaller absoulute
     * value as divisor */
    labs = bigint_abs(l[i]);
    rabs = bigint_abs(r[i]);
    if (bigint_gt(labs, rabs)) {
      d = bigint_div(l[i], r[i]);
      if (bigint_ne(d, op[i]))
        matherr(l[i], r[i], op[i], d, name);
    } else {
      d = bigint_div(r[i], l[i]);
      if (bigint_ne(d, op[i]))
        matherr(r[i], l[i], op[i], d, name);
    }
    bigint_free(labs);
    bigint_free(rabs);
    bigint_free(d);
  }
  stop = clock();
  printf("%s :\t %lf\n", name, (stop - start)/(double)CLOCKS_PER_SEC);
  return (stop - start);
}

clock_t test_sqrt(int size, bigint l[], bigint op[]) {
  char *name = "Sqrt";
  bigint d, abs;
  clock_t stop, start = clock();
  for (int i = 0; i < size; i++) {
    abs = bigint_abs(l[i]);
    d = bigint_sqrt(abs);
    if (bigint_ne(d, op[i]))
      sqrterr(abs, op[i], d, name);
    bigint_free(abs);
    bigint_free(d);
  }
  stop = clock();
  printf("%s :\t %lf\n", name, (stop - start)/(double)CLOCKS_PER_SEC);
  return (stop - start);
}
