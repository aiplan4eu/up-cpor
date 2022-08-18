namespace CPORLib.LogicalUtilities
{
    public class Parameter : Argument
    {
        public Parameter(string sType, string sName)
            : base(sType, sName)
        {
        }
        public Parameter(int iType, string sName)
            : base(iType, sName)
        {
        }
        public new string FullString()
        {
            //return "(" + Name + " " + Type + ")";
            if (Type != "")
                return Name + " - " + Type;

            return Name;
        }



        public override string ToString()
        {
            //return "(" + Name + " " + Type + ")";
            return Name;
        }
    }
}
