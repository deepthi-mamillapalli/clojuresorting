#include<stdio.h>


/*@
	assigns     t[i], t[j];
	ensures     \old(t[i]) == t[j];
	ensures     \old(t[j]) == t[i];
*/

void swap(int *t, int l, int i,int j){
  int tmp;
  tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
  return;
}

/*@ 
	predicate sorted{L}(int *t , integer length) =
	\forall integer i,j; 0 <= i <= j < length ==> (t[i] <= t[j]);
*/

/*@
	requires\valid (t + (0..(l-1)));
	requires l > 0;
	
	behavior sorted:
	ensures (\forall integer a; 0 <= a < l
 	==> (\exists integer b; 0 <= b < l
 	==> \at(t[b],Old) == \at(t[a],Here) ));
	ensures sorted{Here}(t,l-1);

	complete behaviors sorted;
	disjoint behaviors sorted;
*/

void sort(int *t, int l) {
  int i;
  int j;
/*@	
	loop invariant 0 <= i <= l;
	loop assigns i;
	loop invariant \forall integer a,b; 0 <= a <= b < l ==> (t[a] <= t[b]);
	loop variant l-i;
*/
	

  for (i=0;i<l;i++) {
/*@
	
	loop invariant 0 <= j < l;
	loop assigns j,t[0.. l-1];
	loop invariant \forall integer k; (0 <= k < j) ==> (t[k] <= t[j]);
	loop variant l-1-j;
*/
    for (j=0;j<l-1;j++) {
      if (t[j] > t[j+1]) swap(t, l, j, j+1);
    }
  }
}

void affiche(int *t, int l) {
  int i;
  printf("{ ");
  for(i=0;i<l-1;i++) {
    printf("%d, ",t[i]);
  }
  printf("%d}\n",t[i]);
}


/* tester les fonctions de tri    *
 * avant d'essayer de les prouver */
int main() {
  int t[10] = {4,3,8,8,1,0,7,2,9,1};
  affiche(t,10);
  sort(t,10);
  affiche(t,10);
  return 0;
}

