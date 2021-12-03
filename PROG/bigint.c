#include <bigint.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <stdint.h>

// typedefs for 64 bit chunks
typedef uint64_t chunk;
typedef int64_t schunk;
typedef __uint128_t bigchunk;
#define CHUNKMASK 0xFFFFFFFFFFFFFFFFULL

/* Macros */
#define BITSPERCHUNK ((sizeof(chunk)<<3))
#define MAX(a,b) ((a<b)?b:a)

/* A bigint is an array of chunks of bits */
struct bigint_struct 
{
  chunk *blks;        /* pointer to array of bit chunks */
  int size;           /* number of chunks in the array  */
};

/* Private function prototypes */
bigint bigint_adc(bigint l, bigint r, chunk carry);
static bigint bigint_shift_left_chunk(bigint l, int chunks);
void bigint_shift_left_in_place(bigint l, int shamt);
static bigint bigint_shift_right_chunk(bigint l, int chunks);
bigint bigint_trim(bigint b);
bigint bigint_fast_trim(bigint b);
static bigint bigint_mul_uint(bigint l, chunk r);
static bigint bigint_extend(bigint b, int nchunks);
static unsigned bigint_smallmod(bigint b, chunk num);
bigint bigint_alloc(int chunks);

/******************************************************************/
/* Initialization, conversion, and copy functions                 */
/******************************************************************/

/* convert string to bigint */
bigint bigint_from_str(char *s) { 
  bigint d;
  bigint power;
  bigint ten;
  bigint tmp;
  bigint currprod;
  int i, negative = 0;
  d = bigint_from_int(0);
  ten =   bigint_from_int(10);
  power = bigint_from_int(1);
  if (*s == '-') {
    negative = 1;
    s++;
  }
  for (i = strlen(s)-1; i >= 0; i--) {
    if (!isdigit(s[i])) {
      fprintf(stderr,"Cannot convert string to bigint\n");
      exit(1);
    }
    tmp = bigint_from_int(s[i]-'0');
    currprod = bigint_mul(tmp,power);
    bigint_free(tmp);
    tmp = bigint_adc(currprod,d,0);
    bigint_free(d);
    d = tmp;
    bigint_free(currprod);
    if (i > 0) {
      tmp = bigint_mul(power,ten);
      bigint_free(power);
      power = tmp;
    }
  }
  if (negative) {
    tmp = bigint_negate(d);
    bigint_free(d);
    d = tmp;
  }
  bigint_free(ten);
  bigint_free(power);
  return d;
}

/* convert integer to bigint */
bigint bigint_from_int(int val) {
  bigint d = bigint_alloc(1);
  d->blks[0] = (val & CHUNKMASK);
  return d;
}

/* duplicate a bigint */
bigint bigint_copy(bigint source) {
  bigint r;
  r = bigint_alloc(source->size);
  memcpy(r->blks, source->blks, r->size * sizeof(chunk));
  return r;
}

/* convert a bigint into and integer, if possible */
int bigint_to_int(bigint b) {
  int i, negative=0, result=0;
  bigint tmp1, tmp2;
  tmp1 = bigint_trim(b); /* make a trimmed copy */
  if (tmp1->size * sizeof(chunk) > sizeof(int)) {
    fprintf(stderr, "Cannot convert bigint to int\n%ld bytes\n",
      (long)tmp1->size * sizeof(chunk));
    exit(1);
  }
  /* check sign and negate if necessary */
  if (tmp1->blks[tmp1->size-1] & ((bigchunk)1<<(BITSPERCHUNK-1))) {
    negative = 1;
    tmp2 = bigint_negate(tmp1);
    bigint_free(tmp1);
    tmp1 = tmp2;
  }
  for (i = tmp1->size-1; i >= 0; i--)
    result |= (tmp1->blks[i]<<(i*BITSPERCHUNK));
  bigint_free(tmp1);
  if (negative)
    result = -result;
  return result;
}

/* convert a bigint to a string */
char *bigint_to_str(bigint b) {
  int negative = 0;
  unsigned remainder;
  char *s, *r;
  bigint tmp, tmp2;
  /* rough estimate of the number of characters needed */
  int chars = log10(pow(2.0, (b->size * BITSPERCHUNK)))+3;
  int i = chars-1;
  if ((s = (char*)malloc(1 + chars * sizeof(char))) == NULL) {
    perror("bigint_str");
    exit(1);
  }
  s[i] = 0;   /* set last character to ASCII null */
  tmp = bigint_copy(b);
  if (b->blks[tmp->size-1] & ((bigchunk)1<< (BITSPERCHUNK-1))) {
    negative = 1;
    tmp2 = bigint_negate(tmp);
    bigint_free(tmp);
    tmp = tmp2;
  }
  if (bigint_is_zero(tmp)) {
    s[--i] = '0';
  } else {
    do {
      remainder = bigint_smallmod(tmp, 10);
      s[--i] = remainder + '0';
    } while(!bigint_is_zero(tmp));
    if (negative)
      s[--i] = '-';
  }
  r = strdup(s + i);
  bigint_free(tmp);
  free(s);
  return r;
}

/* destroy a bigint */
void bigint_free(bigint b) {
  if (b != NULL) {
    if (b->blks != NULL)
      free(b->blks);
    free(b);
  }
}

/******************************************************************/
/* Mathematical operations                                        */
/******************************************************************/

/* this is the internal add function.  It includes a    */
/* carry. Several other functions use it.               */
#ifndef USE_ASM
 bigint bigint_adc(bigint l, bigint r, chunk carry) {
  bigint sum, tmpl, tmpr;
  int i, nchunks;
  bigchunk tmpsum;
  /* allocate one extra chunk to make sure overflow
     cannot occur */
  nchunks = MAX(l->size, r->size) + 1;
  /* make sure both operands are the same size */
  tmpl = bigint_extend(l, nchunks);
  tmpr = bigint_extend(r, nchunks);
  /* allocate space for the result */
  sum = bigint_alloc(nchunks);
  /* perform the addition */
  for (i = 0; i < nchunks; i++) {
    /* add the current block of bits */
    tmpsum = (bigchunk)tmpl->blks[i] + (bigchunk)tmpr->blks[i] + (bigchunk)carry;
    sum->blks[i] = tmpsum & CHUNKMASK;
    /* calculate the carry bit for the next block */
    carry = (tmpsum >> BITSPERCHUNK) & CHUNKMASK;
  }
  bigint_free(tmpl);
  bigint_free(tmpr);
  tmpl = bigint_trim(sum);
  bigint_free(sum);
  return tmpl;
}
#endif

/* The add function calls adc to perform an add with    */
/* initial carry of zero */    
#ifndef USE_ASM                           
bigint bigint_add(bigint l, bigint r) {
  return bigint_adc(l, r, 0);
}
#endif

/* The complement function returns the 1's complement */
bigint bigint_complement(bigint b) {
  bigint r = bigint_copy(b);
  for (int i = 0; i < r->size; i++)
    r->blks[i] ^= CHUNKMASK;
  return r;
}

/* The sub function gets the 1's complement of r, and adds it to l
   with an initial carry of 1. The initial carry is equivalent to
   adding 1 to the 1's complement to create the 2's complement.
*/
bigint bigint_sub(bigint l, bigint r) {
  bigint tmp1, tmp2;
  tmp1 = bigint_complement(r);
  tmp2 = bigint_adc(l, tmp1, 1);
  bigint_free(tmp1);
  return tmp2;
}

/* The mul_uint function multiplies a bigint by an unsigned chunk */
static bigint bigint_mul_uint(bigint l, chunk r) {
  int i, negative = 0;
  bigchunk tmpchunk;
  bigint sum = bigint_from_int(0);
  bigint tmp1, tmp2;
  /* make sure the left operand is not negative */
  if (l->blks[l->size-1] & ((bigchunk)1<<(BITSPERCHUNK-1))) {
    negative ^= 1;
    l = bigint_negate(l);
  }
  /* Perform the multiply (See section 7.2.5) */
  for (i = 0; i < l->size; i++) {
    tmpchunk = (bigchunk)l->blks[i] * r;
    tmp1 = bigint_alloc(3);
    tmp1->blks[0] = tmpchunk & CHUNKMASK;
    tmp1->blks[1] = (tmpchunk>>BITSPERCHUNK) & CHUNKMASK;
    tmp1->blks[2] = 0;
    tmp2 = bigint_shift_left_chunk(tmp1, i);
    bigint_free(tmp1);
    tmp1 = bigint_adc(sum, tmp2, 0);
    bigint_free(sum);
    bigint_free(tmp2);
    sum = tmp1;
  }
  /* result may need to be negated */
  if (negative) {
    tmp1 = sum;
    sum = bigint_negate(sum);
    bigint_free(tmp1);
    bigint_free(l);
  }
  return sum;
}

/* bigint_mul uses the algorithm from Section 7.2.5     */
bigint bigint_mul(bigint l, bigint r) {
  int i, negative = 0;
  /* the result may require the sum
     of the number of chunks in l and r */
  bigint sum = bigint_from_int(0);
  bigint tmp1, tmp2;
  /* make sure the right operand is not negative */
  if (r->blks[r->size-1] & ((bigchunk)1<<(BITSPERCHUNK-1))) {
    negative = 1;
    r = bigint_negate(r);     /* make negated copy of r */
  }
  for (i = 0; i < r->size; i++) {
    tmp1 = bigint_mul_uint(l,r->blks[i]);
    tmp2 = bigint_shift_left_chunk(tmp1,i);
    bigint_free(tmp1);
    tmp1 = sum;
    sum = bigint_adc(sum,tmp2,0);
    bigint_free(tmp1);
    bigint_free(tmp2);
  }
  if (negative) {
    tmp1 = sum;               /* copy original */
    sum = bigint_negate(sum); /* create complement */
    bigint_free(tmp1);        /* free original */
    bigint_free(r);
  }
  return sum;
}

/* bigint_div uses the algorithm from Section 7.3.2. */
bigint bigint_div(bigint l, bigint r) {
  bigint lt = bigint_trim(l);
  bigint rt = bigint_trim(r);

  bigint tmp,q = bigint_from_int(0);
  int shift, chunkshift, negative = 0;
  if (lt->size < rt->size) {
    bigint_free(lt);
    bigint_free(rt);
    return q; 
  }
  /* make sure the right operand is not negative */
  if (r->blks[r->size-1] & ((bigchunk)1<<(BITSPERCHUNK-1))) {
    negative = 1;  /* track sign of result */
    tmp = rt;
    rt = bigint_negate(rt);
    bigint_free(tmp);
  }
  /* make sure the left operand is not negative */
  if (l->blks[l->size-1] & ((bigchunk)1<<(BITSPERCHUNK-1))) {
    negative ^= 1;  /* track sign of result */
    tmp = lt;
    lt = bigint_negate(lt);
    bigint_free(tmp);
  }
  /* do shift by chunks */
  chunkshift = lt->size - rt->size;
  if (chunkshift > 0) {
    tmp = rt;
    rt = bigint_shift_left_chunk(rt, chunkshift);
    bigint_free(tmp);
  }
  /* do remaining shift bit-by-bit */
  shift = 0;
  while ((shift < (BITSPERCHUNK-1)) && bigint_lt(rt, lt)) {
    shift++;
    tmp = rt;
    rt = bigint_shift_left(rt, 1);
    bigint_free(tmp);
  }
  shift += (chunkshift * BITSPERCHUNK); /* Calculate total shift */
  /* loop to shift right and subtract */
  while (shift >= 0) {
    tmp = q;
    q = bigint_shift_left(q, 1);
    bigint_free(tmp);
    if (bigint_le(rt, lt)) {
      /* perform subtraction */
      tmp = lt;
      lt = bigint_sub(lt,rt);
      bigint_free(tmp);
      /* change lsb from zero to one */
      q->blks[0] |= 1;
    }
    tmp = rt;
    rt = bigint_shift_right(rt,1);
    bigint_free(tmp);
    shift--;
  }
  /* correct the sign of the result */
  if (negative) {
    tmp = bigint_negate(q);
    bigint_free(q);
    q = tmp;
  }
  bigint_free(rt);
  bigint_free(lt);
  return q;
}

/* The C version of bigint_negate is very short, because it uses
   existing functions.  However, it is not very efficient. We also
   have an assembly version of the negate function. The #ifndef 
   allows us to use the assembly version. When USE_ASM is defined,
   the C version will not be compiled. */

#ifndef USE_ASM
bigint bigint_negate(bigint b) {
  bigint r = bigint_complement(b);   /* get 1's complement */
  bigint tmp1 = bigint_from_int(0);  /* create zero */
  bigint tmp2 = bigint_adc(r, tmp1, 1); /* add with an initial carry */
  bigint_free(tmp1);
  bigint_free(r);
  return tmp2;
}
#endif

/* The add function calls adc to perform an add with    */
/* initial carry of zero                                */
bigint bigint_abs(bigint b) {
  if (b->blks[b->size-1] & ((bigchunk)1<<(BITSPERCHUNK-1)))
    return bigint_negate(b);
  else
    return bigint_copy(b);
}


/* The sqrt function returns floor(sqrt(b)) using the digit-by-digit */
bigint bigint_sqrt(bigint b) {
  bigint r = bigint_from_int(0), zero = bigint_from_int(0);
  bigint num = bigint_copy(b), tmp, resplusbit, bit;
  if (b->blks[b->size-1] & ((bigchunk)1<<(BITSPERCHUNK-1))) {
    fprintf(stderr,
      "Cannot compute square root of negative number.\n");
    exit(1);
  }

  
  bit = bigint_alloc(b->size);
  bit->blks[bit->size-1] = ((bigchunk)1<<(BITSPERCHUNK-2));
  for (int i = 0; i < bit->size-1; i++)
    bit->blks[i] = 0;
  while (bit->blks[bit->size-1] > b->blks[b->size-1])
    bit->blks[bit->size-1] >>= 2;
  if (bit->blks[bit->size-1] == 0)
    bit->blks[bit->size-2] = ((bigchunk)1<<(BITSPERCHUNK-2));
  
  while (bigint_gt(bit,zero)) {
    resplusbit = bigint_add(r, bit);
    if (bigint_ge(num,resplusbit)) {
      tmp = num;
      num = bigint_sub(num,resplusbit);
      bigint_free(tmp);
      tmp = bigint_shift_right(r,1);
      bigint_free(r);
      r = bigint_add(tmp,bit);
      bigint_free(tmp);
    } else {
      tmp = r;
      r = bigint_shift_right(r,1);
      bigint_free(tmp);
    }
    bigint_free(resplusbit);
    tmp = bit;
    bit = bigint_shift_right(bit,2);
    bigint_free(tmp);
  }
  bigint_free(zero);
  bigint_free(num);
  bigint_free(bit);
  return r;
}


/* shift left by entire chunks */
static bigint bigint_shift_left_chunk(bigint l, int chunks) {
  bigint tmp = bigint_alloc(l->size + chunks);
  for (int i = -chunks; i < l->size; i++) {
    if (i < 0)
      tmp->blks[i+chunks] = 0;
    else
      tmp->blks[i+chunks] = l->blks[i];
  }
  return tmp;
}

/* shift right by entire chunks */
static bigint bigint_shift_right_chunk(bigint l, int chunks) {
  bigint tmp = bigint_alloc(l->size - chunks);
  for (int i = 0; i < tmp->size; i++) {
    if (i<chunks)
      tmp->blks[i] = 0;   // should do sign extend // TODO comment
    else
      tmp->blks[i]=l->blks[i-chunks];
  }
  return tmp;
}

/* Shift left the given about.  This will shift by chunks as much as
   it can, then finish off with a sub-chunk shift. */
bigint bigint_shift_left(bigint l, int shamt) {

  int sz = (l->size)+1;
  l = bigint_extend(l, (shamt>>6)+sz);
  int extra = (shamt & 0x000000000000003F);
  shamt = (shamt>>6);
  if (shamt) {
  for (int i = -shamt; i < sz; i++) {
    if (i < 0)
      l->blks[i+shamt] = 0;
    else
      l->blks[i+shamt] = l->blks[i];
  }

  }
  if (extra) {
    for (int i = l->size - 1; i > 0; i--) {
      l->blks[i] =
        (l->blks[i]<<extra) | (l->blks[i-1]>>(BITSPERCHUNK-extra));
    }
    l->blks[0] = (l->blks[0] << extra);
  }
  bigint_fast_trim(l);
  return l;
}

void bigint_shift_left_in_place(bigint l, int shamt) 
{
  int sz = (l->size)+1;
  l = bigint_extend(l, (shamt>>6)+sz);
  int extra = (shamt & 0x000000000000003F);
  shamt = (shamt>>6);
  if (shamt) {
  for (int i = -shamt; i < sz; i++) {
    if (i < 0)
      l->blks[i+shamt] = 0;
    else
      l->blks[i+shamt] = l->blks[i];
  }

  }
  if (extra) {
    for (int i = l->size - 1; i > 0; i--) {
      l->blks[i] =
        (l->blks[i]<<extra) | (l->blks[i-1]>>(BITSPERCHUNK-extra));
    }
    l->blks[0] = (l->blks[0] << extra);
  }
  bigint_fast_trim(l);
}
/* Arithmetic shift right the given about.  This will shift by
   chunks as much as it can, then finish off with a sub-chunk
   shift. */
bigint bigint_shift_right(bigint l, int shamt) {
  schunk tmpc;
  int extra = (shamt % 64);
  shamt = (shamt/64);
 
  if (shamt > 0) {
    l = bigint_shift_right_chunk(l, shamt);
  }
  l = bigint_trim(l);
  //bigint tmp = bigint_alloc(l->size - chunks);
  //for (int i = 0; i < (l->size - shamt); i++) {
  //  if (i<shamt)
  //    l->blks[i] = 0;   // should do sign extend // TODO comment
  //  else
  //    l->blks[i]=l->blks[i-shamt];
  //}
  
  //l->size = (l->size - shamt);

  for (int i = 0; i < l->size; i++) {
    if (i < shamt){
        l->blks[i] = 0;   // should do sign extend // TODO comment
    }
    else{
        l->blks[i]=l->blks[i-shamt];
    }
  }
  if (extra) {
    for (int i = 0; i < l->size-1; i++) {
      l->blks[i] =
        (l->blks[i]>>extra) | (l->blks[i+1]<<(BITSPERCHUNK-extra));
    }
    /* do a signed shift of the top chunk */
    tmpc = l->blks[l->size - 1];
    tmpc >>= extra;
    l->blks[l->size - 1] = tmpc;
  }
  bigint_fast_trim(l);
  return l;
}

/******************************************************************/
/* Test and compare operatioins                                   */
/******************************************************************/

/* Compare bigint to zero */
inline int bigint_is_zero(bigint b) {
  for (int i = 0; i < b->size; i++)
    if (b->blks[i])
      return 0;
  return 1;
}

inline int bigint_le(bigint l, bigint r) {
  return (bigint_cmp(l, r) < 1);
}

inline int bigint_lt(bigint l, bigint r) {
  return (bigint_cmp(l, r) == -1);
}

inline int bigint_ge(bigint l, bigint r) {
  return (bigint_cmp(l, r) > -1);
}

inline int bigint_gt(bigint l, bigint r) {
  return (bigint_cmp(l, r) == 1);
}

inline int bigint_eq(bigint l, bigint r) {
  return (!bigint_cmp(l, r));
}

inline int bigint_ne(bigint l, bigint r) {
  return abs(bigint_cmp(l, r));
}

/* bigint_cmp is the core of all of the comparisons */
#ifndef USE_ASM
int bigint_cmp(bigint l, bigint r) {
  bigint d = bigint_sub(l,r);
  int cmp;
  if ((d->size == 0) || (d->size == 1 && d->blks[0] == 0)) {
    cmp = 0;    // d == 0
  } else if (d->blks[d->size-1] & ((bigchunk)1 << (BITSPERCHUNK-1))) {
    cmp = -1;   // d < 0 (MSB == 1)
  } else {
    cmp = 1;    // d > 0
  }
  bigint_free(d);
  return cmp;
}
#endif

/******************************************************************/
/* Functions for binary input/output                              */
/******************************************************************/

void bigint_write_binary(FILE *f,bigint x) {
  if (fwrite(&(x->size), sizeof(x->size), 1, f) != 1) {
    perror("Write failed");
    exit(4);
  }
  if (fwrite(x->blks, sizeof(chunk), x->size, f) != x->size) {
    perror("Write failed");
    exit(4);
  }
}

bigint bigint_read_binary(FILE *f) {
  bigint r = (bigint) malloc(sizeof(struct bigint_struct));
  if (r == NULL) {
    perror("bigint_read_binary");
    exit(1);
  }
  if (fread(&(r->size), sizeof(r->size), 1, f) != 1) {
    free(r);
    return NULL;
  }
  r->blks = (chunk *) malloc(r->size * sizeof(chunk));
  if (r->blks == NULL) {
    perror("bigint_read_binary");
    exit(2);
  }
  if (fread(r->blks, sizeof(chunk), r->size, f) != r->size) {
    perror("Unable to read from file");
    exit(4);
  }
  return r;
}

/******************************************************************/
/*  Utility functions                                             */
/******************************************************************/

bigint bigint_alloc(int chunks) 
{
  bigint r = (bigint) malloc(sizeof(struct bigint_struct));
  if (r == NULL) {
    perror("bigint_alloc");
    exit(1);
  }
  r->size = chunks;
  r->blks = (chunk*) malloc(chunks * sizeof(chunk));
  if (r->blks == NULL) {
    perror("bigint_alloc");
    exit(1);
  }
  return r;
}

bigint bigint_trim(bigint b) {
  bigint d;
  int i = b->size-1;
  if (i > 0) {
    if (b->blks[i] == 0) {
      // we have a leading block that is all 0
      do
        i--; // search for first block that is not all 0
      while ((i > 0) && (b->blks[i] == 0));
      if (b->blks[i] & ((bigchunk)1<<(BITSPERCHUNK-1)))
        i++;  // if msb of current block is 1, then we went too far
    }
    else if (b->blks[i] == CHUNKMASK) { 
      // we have a leading block that is all 1
      do
	i--; // search for first block that is not all 1
      while ((i>0) && (b->blks[i]==CHUNKMASK));
      if (!(b->blks[i] & ((bigchunk)1<<(BITSPERCHUNK-1))))
	i++;  // if msb of current block is 0, then we went too far
    }
  }
  i++;  // i is now the number of blocks to copy
  if (i < b->size) {
    d = bigint_alloc(i);
    memcpy(d->blks,b->blks,d->size*sizeof(chunk));
  } else {
    d = bigint_copy(b);
  }
  return d;
}

bigint bigint_fast_trim(bigint b) {
  int i = b->size-1;
  if (i > 0) {
    if (b->blks[i] == 0) {
      // we have a leading block that is all 0
      do
        i--; // search for first block that is not all 0
      while ((i > 0) && (b->blks[i] == 0));
      if (b->blks[i] & ((bigchunk)1<<(BITSPERCHUNK-1)))
        i++;  // if msb of current block is 1, then we went too far
    }
    else if (b->blks[i] == CHUNKMASK) { 
      // we have a leading block that is all 1
      do
	i--; // search for first block that is not all 1
      while ((i>0) && (b->blks[i]==CHUNKMASK));
      if (!(b->blks[i] & ((bigchunk)1<<(BITSPERCHUNK-1))))
	i++;  // if msb of current block is 0, then we went too far
    }
  }
  i++;  // i is now the number of blocks to copy
  if (i < b->size) {
    b->size = i;
  } 
  return b;
}
/* smallmod divides a bigint by a small number
   and returns the modulus. b changes as a SIDE-EFFECT.
   This is used by the to_str function. */
static unsigned bigint_smallmod(bigint b, chunk num) {
  bigchunk tmp;
  int i;
  if (num >= ((bigchunk)1<<(BITSPERCHUNK-1))) {
    fprintf(stderr,"bigint_smallmod: divisor out of range\n");
    exit(1);
  }
  /* start with most significant chunk and work down, taking
     two overlapping chunks at a time */
  tmp = b->blks[b->size-1];
  for(i = b->size-1; i > 0; i--) {
    b->blks[i] = tmp/num;
    tmp = ((tmp % num) << BITSPERCHUNK) | b->blks[i-1];
  }
  b->blks[0] = tmp / num;
  tmp = tmp % num;
  return tmp;
}

static bigint bigint_extend(bigint b, int nchunks) {
  bigint tmp;
  int i, negative;
  negative = 0;
  if (b->blks[b->size-1] & ((bigchunk)1<<(BITSPERCHUNK-1)))
    negative = 1;
  tmp = bigint_alloc(nchunks);
  for (i = 0; i < nchunks; i++) {
    if (i < b->size)
      tmp->blks[i] = b->blks[i];
    else if (negative)
      tmp->blks[i] = CHUNKMASK;
    else
      tmp->blks[i] = 0;
  }
  return tmp;
}
