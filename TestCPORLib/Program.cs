using CPORLib;




public class Program
{
    public static void RunTest(string sName)
    {
        string sPath = @"C:\Users\shanigu\OneDrive - Ben Gurion University of the Negev\Research\projects\AIPlan4EU\up-cpor\Tests\" + sName;
        string sDomainFile = Path.Combine(sPath, "d.pddl");
            string sProblemFile = Path.Combine(sPath, "p.pddl");
            Run.RunPlanner(sDomainFile
                , sProblemFile,
                false);
    }
    public static void TestAll()
    {
        RunTest("localize5");
        RunTest("colorballs2-2");
        RunTest("doors5");
        RunTest("medpks010");
        RunTest("unix1");
    }

    private static void Main(string[] args)
    {
        //TestAll();
        //return;


        if (args.Length < 2)
        {
            Console.WriteLine("Usage: RunPlanner domain_file problem_file [online/offline]");
        }
        else
        {
            string sDomainFile = args[0];
            string sProblemFile = args[1];
            bool bOnline = false;
            if (args.Length > 2)
                bOnline = args[2] == "online";
            Run.RunPlanner(sDomainFile
                , sProblemFile,
                bOnline);
        }
    }
}