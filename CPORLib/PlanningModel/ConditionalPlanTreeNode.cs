using System.Collections.Generic;
using System;

namespace CPORLib.PlanningModel
{
    public class ConditionalPlanTreeNode
    {
        public int ID { get; set; }

        public int IndexInPlanFile { get; set; }

        private PlanningAction m_aAction;
        public PlanningAction Action {
            get
            {
                return m_aAction;
            }
            set
            {
                m_aAction = value;
            }
        }

        private ConditionalPlanTreeNode m_nChild;

        public ConditionalPlanTreeNode SingleChild {
            get 
            { 
                return m_nChild; 
            }
            set
            {
                //if(ID == 10)
                 //   Console.Write("*");
                m_nChild = value;
            }
        }
        public ConditionalPlanTreeNode FalseObservationChild { get; set; }
        public ConditionalPlanTreeNode TrueObservationChild { get; set; }
        public bool DeadEnd { get; set; }
        public bool Goal { get; set; }

        private static int CountNodes = 0;

        public ConditionalPlanTreeNode()
        {
            ID = CountNodes++;
            //if (ID == 174)
            //    Debug.Write("*");
        }

        private string ToTreeString(string sIndent, HashSet<int> lHistory)
        {
            if (lHistory.Contains(ID))
                return sIndent + ID + ") connect to " + ID;
            //HashSet<int> lNewHistory = new HashSet<int>(lHistory);
            lHistory.Add(ID);
            if (DeadEnd)
                return sIndent + ID + ") deadEnd \n\n";
            if (Goal)
                return sIndent + ID + ") goal \n\n";

            string s = sIndent + ID + ") " + Action.Name + "\n";
            if (SingleChild != null)
                s += SingleChild.ToTreeString(sIndent, lHistory);
            else
            {
                s += "branching...\n";
                if (FalseObservationChild != null)
                    s += FalseObservationChild.ToTreeString(sIndent + "\t", lHistory);
                else
                    s += "Can't be false";
                s += "\n";
                if (TrueObservationChild != null)
                    s += TrueObservationChild.ToTreeString(sIndent + "\t", lHistory);
                else
                    s += "Can't be true";
            }
            return s;
        }

        private string ToStringSimple()
        {
            if (DeadEnd)
                return ID + ") deadEnd";
            if (Goal)
                return ID + ") goal";
            if (Action == null)
                return ID + ") fail";
            string s = ID + ") " + Action.Name + ", children={";
            if (SingleChild != null)
                s += SingleChild.ID;
            else
            {

                if (FalseObservationChild != null)
                    s += FalseObservationChild.ID;
                else
                    s += "Can't be false";
                s += ", ";
                if (TrueObservationChild != null)
                    s += TrueObservationChild.ID;
                else
                    s += "Can't be true";
            }
            s += "}";
            return s;
        }

        public override int GetHashCode()
        {
            return ID;
        }

        public override string ToString()
        {
            return ToStringSimple();
            //return ToString("", new HashSet<int>());
        }
    }
}
