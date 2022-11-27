using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace CPORLib.FFCS
{
    public class Inertia
    {
        /* stores inertia - information: is any occurence of the predicate
 * added / deleted in the uninstantiated ops ?
 */
        public  bool[] gis_added = new bool[Constants.MAX_PREDICATES];
        public  bool[] gis_deleted = new bool[Constants.MAX_PREDICATES];






        /* the type numbers corresponding to any unary inertia
         */
        public  int[] gtype_to_predicate = new int[Constants.MAX_PREDICATES];
        public  int[] gpredicate_to_type = new int[Constants.MAX_TYPES];

        /* (ordered) numbers of types that new type is intersection of
         */
        public  TypeArray[] gintersected_types = new TypeArray[Constants.MAX_TYPES];
        public  int[] gnum_intersected_types = new int[Constants.MAX_TYPES];


    }

}
