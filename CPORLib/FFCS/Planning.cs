using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace CPORLib.FFCS
{

    public class Planning
    {

        /* the effects that are considered true in relaxed plan
         */
        public int[] gin_plan_E;
        public int gnum_in_plan_E;



        /* always stores (current) serial plan
         */
        public int[] gplan_ops = new int[Constants.MAX_PLAN_LENGTH];
        public int gnum_plan_ops = 0;



        /* stores the states that the current plan goes throuFF.Search.gH
         * ( for knowing where new agenda entry starts from )
         */
        public FFState[] gplan_states = new FFState[Constants.MAX_PLAN_LENGTH + 1];



        public int[] gaxdels;
        public int gnum_axdels;

        public int gnum_strata;



    }

}
