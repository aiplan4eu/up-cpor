using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace CPORLib.FFCS
{

    public class DomainProperties
    {
        /* splitted domain: hard n easy ops
 */
        public  Operator[] ghard_operators;
        public  int gnum_hard_operators;
        public  NormOperator[] geasy_operators;
        public  int gnum_easy_operators;


        /* so called Templates for easy ops: possible inertia constrained
         * instantiation constants
         */
        public  EasyTemplate geasy_templates;
        public  int gnum_easy_templates;



        /* first step for hard ops: create mixed operators, with conjunctive
         * precondition and arbitrary effects
         */
        public  MixedOperator  ghard_mixed_operators;
        public  int gnum_hard_mixed_operators;



        /* hard ''templates'' : pseudo actions
         */
        public  PseudoAction[] ghard_templates;
        public  int gnum_hard_templates;



        /* store the final "relevant facts"
         */
        public  InitializedArray<Fact> grelevant_facts = new InitializedArray<Fact>(Constants.MAX_RELEVANT_FACTS);
        public  int gnum_relevant_facts = 0;
        public  int gnum_pp_facts = 0;



        /* the final actions and problem representation
         */
        public  Action gactions;
        public  int gnum_actions;
        public  FFState ginitial_state;
        public  FFState ggoal_state;

        /* global arrays of constant names,
 *               type names (with their constants),
 *               predicate names,
 *               predicate aritys,
 *               defined types of predicate args
 */
        public  string[] gconstants = new string[Constants.MAX_CONSTANTS];
        public  int gnum_constants = 0;
        public  string[] gtype_names = new string[Constants.MAX_TYPES];
        public  int[,] gtype_consts = new int[Constants.MAX_TYPES, Constants.MAX_TYPE];
        public  bool[,] gis_member = new bool[Constants.MAX_CONSTANTS, Constants.MAX_TYPES];
        public  int[] gtype_size = new int[Constants.MAX_TYPES];
        public  int gnum_types = 0;
        public  string[] gpredicates = new string[Constants.MAX_PREDICATES];
        public  int[] garity = new int[Constants.MAX_PREDICATES];
        public  int[,] gpredicates_args_type = new int[Constants.MAX_PREDICATES, Constants.MAX_ARITY];
        public  int gnum_predicates = 0;
        public  bool[] gderived = new bool[Constants.MAX_PREDICATES];


        /* splitted initial state:
         * initial non  facts,
         * initial  facts, divided into predicates
         * (will be two dimensional array, allocated directly before need)
         */
        public  Facts ginitial = null;
        public  int gnum_initial = 0;
        public  Array2D<Fact> ginitial_predicate;
        public  int[] gnum_initial_predicate;



        /* the domain in integer (Fact) representation
         */
        public  Operator[] goperators = new Operator[Constants.MAX_OPERATORS];
        public  int gnum_operators = 0;
        public  Fact[] gfull_initial;
        public  int gnum_full_initial = 0;
        public  WffNode ggoal = null;

        /* connection to instantiation ( except ops, goal, initial )
 */

        /* all typed objects 
         */
        public  FactList gorig_constant_list = null;

        /* the predicates and their types
         */
        public  FactList gpredicates_and_types = null;

    }


}
