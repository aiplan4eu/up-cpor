using System.Collections.Generic;

namespace CPOR
{
    public class Argument
    {
        public string Name { get { return Names[m_iName]; } set { SetName(value); } }
        public string Type { get { return Types[m_iType]; } set { SetType(value); } }

        private void SetType(string sType)
        {
            m_iType = Types.IndexOf(sType);
            if (m_iType == -1)
            {
                m_iType = Types.Count;
                Types.Add(sType);
            }
        }
        private void SetName(string sName)
        {
            m_iName = Names.IndexOf(sName);
            if (m_iName == -1)
            {
                m_iName = Names.Count;
                Names.Add(sName);
            }
        }

        protected int m_iType;
        protected int m_iName;

        protected static List<string> Types = new List<string>();
        protected static List<string> Names = new List<string>();

        public Argument(string sType, string sName)
        {
            SetName(sName);
            SetType(sType);
        }
        public Argument(int iType, string sName)
        {
            SetName(sName);
            m_iType = iType;
        }
        public string FullString()
        {
            return Name + " - " + Type;
        }
        public override string ToString()
        {
            return Name;
        }
        public override sealed int GetHashCode()
        {
            return m_iType * 100 + m_iName;
        }
        public override sealed bool Equals(object obj)
        {
            if (obj is Argument)
            {
                Argument arg = (Argument)obj;
                return arg.m_iType == m_iType && arg.m_iName == m_iName;
            }
            return false;
        }
    }
}
