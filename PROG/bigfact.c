#include <bigint.h>
#include <stdio.h>
#include <stdlib.h>

bigint bigfact(bigint x)
{
  bigint tmp1 = bigint_from_int(1);
  bigint tmp2;
  if(bigint_le(x,tmp1))
    return tmp1;
  tmp2 = bigint_sub(x,tmp1);
  bigint_free(tmp1);
  tmp1 = bigfact(tmp2);
  bigint_free(tmp2);
  tmp2 = bigint_mul(x,tmp1);
  bigint_free(tmp1);
  return tmp2;
}

int main()
{
  bigint a;
  char *s;
  int i,j;
  bigint factable[151];

  for(i=0;i<151;i++)
    {
      a = bigint_from_int(i);
      factable[i] = bigfact(a);
      bigint_free(a);
    }

  for(i=0;i<151;i++)
    {
      s = bigint_to_str(factable[i]);
      printf("%4d %s\n",i,s);
      free(s);
    }

  return 0;
}



