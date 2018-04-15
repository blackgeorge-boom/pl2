
typedef struct list_ {
	int element;
	struct list_ *next;
} list;

/*@ 
  inductive reachable {L} (list *root, list *node) {
 	case root_reachable:
   		\forall list *root; reachable(root, root);
	case next_reachable:
		\forall list *root, *node;
		\valid(root) ==> reachable(root->next, node) ==> reachable(root, node);
  }
*/

/*@
   predicate finite {L} (list *root) = reachable (root, \null); 
*/


/*@ 
   axiomatic length {

   		logic integer length {L} (list *l);

		axiom length_nil {L} : length(\null) == 0;

		axiom length_cons {L} : 
			\forall list *l ,integer n; 
				finite(l) && \valid(l) ==> length(l) == length(l->next) + 1;
	}
*/

/*@
   requires \valid(root);
   terminates finite(root);
   assigns \nothing;
   ensures
   	\forall list *l;
		\valid(l) && reachable(root, l) ==> \result >= l->element;
   ensures
   	\exists list *l;
		\valid(l) && reachable(root, l) ==> \result == l->element;
*/
int max_list (list *root) {

	int max = root->element;

	while (!root->next) {
		root = root->next;
		if (max > root->element) max = root->element;
	}

	return max;
}
