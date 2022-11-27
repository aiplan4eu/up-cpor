using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace CPORLib.FFCS
{

    public class Parsing
    {
        /* used for pddl parsing, flex only allows global variables
 */
        public int gbracket_count;
        public string gproblem_name;

        /* The current input line number
         */
        public int lineno = 1;

        /* The current input filename
         */
        public string gact_filename;

        /* The pddl domain name
         */
        public string gdomain_name;

        /* loaded, uninstantiated operators
         */
        public PlOperator gloaded_ops = null;

        /* stores initials as fact_list 
         */
        public PlNode gorig_initial_facts = null;

        /* not yet preprocessed goal facts
         */
        public PlNode gorig_goal_facts = null;

        /* axioms as in UCPOP before being changed to ops
         */
        public PlOperator gloaded_axioms = null;

        /* the types, as defined in the domain file
         */
        public TypedList gparse_types = null;

        /* the constants, as defined in domain file
         */
        public TypedList gparse_constants = null;

        /* the predicates and their arg types, as defined in the domain file
         */
        public TypedListList gparse_predicates = null;

        /* the objects, declared in the problem file
         */
        public TypedList gparse_objects = null;
    }


}
