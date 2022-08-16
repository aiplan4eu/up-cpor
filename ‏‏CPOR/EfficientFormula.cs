using System;
using System.Collections.Generic;

namespace CPOR
{
    public class EfficientFormula
    {
        public enum Operators { And, Or, Oneof };
        private List<int> m_lAssignments, m_lOriginalAssignments;
        private int m_cRelevantVariables;
        private bool m_bTrue, m_bFalse;
        public Operators Operator { get; private set; }
        public CompoundFormula OriginalFormula { get; set; }

        public EfficientFormula(int cVariables, string sOperator)
        {
            m_lAssignments = new List<int>();
            m_lOriginalAssignments = new List<int>();
            if (sOperator == "and")
                Operator = Operators.And;
            else if (sOperator == "or")
                Operator = Operators.Or;
            else if (sOperator == "oneof")
                Operator = Operators.Oneof;
            else
                throw new InvalidOperationException();
            m_bTrue = false;
            m_bFalse = false;
        }
        public EfficientFormula(string sOperator)
            : this(100000, sOperator)
        {

        }
        public void SetVariableValue(int iVariable, bool bPositive)
        {
            int iAssignment = iVariable * 2;
            if (!bPositive)
                iAssignment++;
            m_lAssignments.Add(iAssignment);
            m_lOriginalAssignments.Add(iAssignment);
            m_cRelevantVariables++;
        }

        public int GetAssignment(int iVariable)
        {
            foreach (int iAssignment in m_lAssignments)
                if (iAssignment / 2 == iVariable)
                    return iAssignment;

            return -1;
        }
        public bool IsVariableRelevant(int iVariable)
        {
            return GetAssignment(iVariable) != -1;
        }

        public bool IsPositive(int iVariable)
        {
            int iAssignment = GetAssignment(iVariable);

            return iAssignment != -1 && iAssignment % 2 == 0;
        }
        public bool IsNegative(int iVariable)
        {
            int iAssignment = GetAssignment(iVariable);

            return iAssignment != -1 && iAssignment % 2 == 1;
        }

        public bool Reduce(int iVariable, bool bPositive, List<int> lLearned)
        {
            if (!IsVariableRelevant(iVariable))
                return false;
#if DEBUG
            if (m_bTrue)
                throw new InvalidOperationException();
            if (m_bFalse)
                throw new InvalidOperationException();
#endif

            if (Operator == Operators.And)
            {
                if (IsPositive(iVariable) && !bPositive)
                    m_bFalse = true;
                else if (IsNegative(iVariable) && bPositive)
                    m_bFalse = true;
                if (m_bFalse)
                    return true;
            }
            else if (Operator == Operators.Or)
            {
                if (IsPositive(iVariable) && bPositive)
                    m_bTrue = true;
                else if (IsNegative(iVariable) && !bPositive)
                    m_bTrue = true;
                if (m_bTrue)
                    return true;
            }
            else if (Operator == Operators.Oneof)
            {
                if ((IsPositive(iVariable) && bPositive) || (IsNegative(iVariable) && !bPositive))
                {
                    foreach (int iAssignment in m_lAssignments)
                    {
                        if (iAssignment != -1 && iAssignment / 2 != iVariable)
                        {
                            if (iAssignment % 2 == 0)
                                lLearned.Add(iAssignment + 1);
                            else
                                lLearned.Add(iAssignment - 1);
                        }
                    }
                    m_bTrue = true;
                    return true;
                }
            }
            for (int i = 0; i < m_lAssignments.Count; i++)
                if (m_lAssignments[i] / 2 == iVariable)
                    m_lAssignments[i] = -1;
            m_cRelevantVariables--;

            if (m_cRelevantVariables == 1)
            {
                foreach (int iAssignment in m_lAssignments)
                {
                    if (iAssignment != -1)
                        lLearned.Add(iAssignment);
                }
                return true;
            }
            return false;
        }

        public bool IsTrue()
        {
            return m_bTrue;
        }
        public bool IsFalse()
        {
            return m_bFalse;
        }
    }
    /*
    public class EfficientFormula
    {
        public enum Operators { And, Or, Oneof };
        private bool[] m_aVariables;
        private int m_cRelevantVariables;
        private bool m_bTrue, m_bFalse;
        private List<int> m_lSetVariables;
        public Operators Operator { get; private set; }
        public CompoundFormula OriginalFormula { get; set; }

        public EfficientFormula(int cVariables, string sOperator)
        {
            long l = GC.GetTotalMemory(true);
            m_aVariables = new bool[cVariables * 2];
            if (sOperator == "and")
                Operator = Operators.And;
            else if (sOperator == "or")
                Operator = Operators.Or;
            else if (sOperator == "oneof")
                Operator = Operators.Oneof;
            else
                throw new InvalidOperationException();
            m_bTrue = false;
            m_bFalse = false;
            m_lSetVariables = new List<int>();
        }
        public EfficientFormula(string sOperator)
            : this(100000, sOperator)
        {

        }
        public void SetVariableValue(int iVariable, bool bPositive)
        {
            if (bPositive)
                m_aVariables[iVariable * 2] = true;
            else
                m_aVariables[iVariable * 2 + 1] = true;
            m_lSetVariables.Add(iVariable);
            m_cRelevantVariables++;
        }

        public bool IsVariableRelevant(int iVariable)
        {
            if (m_aVariables[iVariable * 2] == true || m_aVariables[iVariable * 2 + 1] == true)
                return true;
            return false;
        }

        public bool IsPositive(int iVariable)
        {
            return m_aVariables[iVariable * 2];
        }
        public bool IsNegative(int iVariable)
        {
            return m_aVariables[iVariable * 2 + 1];
        }

        public bool Reduce(int iVariable, bool bPositive, List<int> lLearned)
        {
#if DEBUG
            if (!IsVariableRelevant(iVariable))
                throw new InvalidOperationException();
            if (m_bTrue)
                throw new InvalidOperationException();
            if (m_bFalse)
                throw new InvalidOperationException();
#endif
            Formula cf = OriginalFormula.ToCNF();

            if (Operator == Operators.And)
            {
                if (IsPositive(iVariable) && !bPositive)
                    m_bFalse = true;
                else if (IsNegative(iVariable) && bPositive)
                    m_bFalse = true;
                if (m_bFalse)
                    return true;
            }
            else if (Operator == Operators.Or)
            {
                if (IsPositive(iVariable) && bPositive)
                    m_bTrue = true;
                else if (IsNegative(iVariable) && !bPositive)
                    m_bTrue = true;
                if (m_bTrue)
                    return true;
            }
            else if (Operator == Operators.Oneof)
            {
                if ((IsPositive(iVariable) && bPositive) || (IsNegative(iVariable) && !bPositive))
                {
                    foreach (int iOtherVariable in m_lSetVariables)
                    {
                        if (IsVariableRelevant(iOtherVariable))
                            lLearned.Add(iOtherVariable);
                    }
                    m_bTrue = true;
                }
            }
            m_aVariables[iVariable * 2] = false;
            m_aVariables[iVariable * 2 + 1] = false;
            m_cRelevantVariables--;

            if (m_cRelevantVariables == 1)
            {
                foreach (int iOtherVariable in m_lSetVariables)
                {
                    if (IsVariableRelevant(iOtherVariable))
                        lLearned.Add(iOtherVariable);
                }
                return true;
            }
            return false;
        }

        public bool IsTrue()
        {
            return m_bTrue;
        }
        public bool IsFalse()
        {
            return m_bFalse;
        }
    }
     * */
}
