using CPORLib;
using CPORLib.FFCS;
using System;
using System.IO;

public class Program
{
    public static void RunTest(string sName)
    {
        string sPath = @"..\..\..\..\Tests\" + sName;
        //string sPath = @"C:\Users\Guy\OneDrive - Ben Gurion University of the Negev\Research\projects\AIPlan4EU\up-cpor\Tests\" + sName;
        string sDomainFile = Path.Combine(sPath, "d.pddl");
        string sProblemFile = Path.Combine(sPath, "p.pddl");
        string sOutputFile = Path.Combine(sPath, "out.txt");
        Run.RunPlanner(sDomainFile
            , sProblemFile,
            sOutputFile,
            false, false);
    }
    public static void TestAll()
    {
        FFUtilities.Verbose = true;
        gcmd_line.display_info = 1;
        gcmd_line.debug = 3;
        
        
        RunTest("doors5"); 
        RunTest("blocks3");

              
        RunTest("medpks010");
        RunTest("colorballs2-2");
        RunTest("blocks2");
        RunTest("wumpus05");
        RunTest("unix1");
        RunTest("localize5");


        RunTest("doors15");
        RunTest("wumpus10");
        

        RunTest("blocks3");
        RunTest("blocks2");
        RunTest("wumpus05");
        RunTest("medpks010");
        RunTest("unix1");
        RunTest("localize5");
        RunTest("doors5");
        RunTest("colorballs2-2");   
    }

    public static void Main(string[] args)
    {
        //TestAll();
        //return;

        //TestClassicalFFCS();

        if (args.Length < 3)
        {
            Console.WriteLine("Usage: RunPlanner domain_file problem_file output_file [online/offline]");
        }
        else
        {
            string sDomainFile = args[0];
            string sProblemFile = args[1];
            string sOutputFile = args[2];
            bool bOnline = false;
            if (args.Length > 3)
                bOnline = args[2] == "online";
            Run.RunPlanner(sDomainFile
                , sProblemFile,
                sOutputFile,
                bOnline);
        }
    }

    private static void TestClassicalFFCS()
    {
        string sDomainFile = @"C:\Users\shanigu\Downloads\domain-driver1.pddl";
        string sProblemFile = @"C:\Users\shanigu\Downloads\problem-driver1.pddl";
        MemoryStream ms = new MemoryStream();
        StreamWriter sw = new StreamWriter(ms);
        using (StreamReader sr = new StreamReader(sDomainFile))
        {
            string sDomain = sr.ReadToEnd();
            sw.Write(sDomain);
            sr.Close();
        }
        using (StreamReader sr = new StreamReader(sProblemFile))
        {
            string sProblem = sr.ReadToEnd();
            sw.Write(sProblem);
            sr.Close();
        }
        sw.Flush();
        ms.Position = 0;
        FF ff = new FF(ms);
        List<string> lPlan = ff.Plan();
    }
}