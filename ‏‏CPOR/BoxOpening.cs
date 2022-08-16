using System.IO;

namespace CPOR
{
    class BoxOpening
    {
        public int Boxes { get; set; }
        public int Levers { get; set; }
        public string Name { get { return "Boxes" + Boxes + "_" + Levers; } }

        public BoxOpening(int cBoxes, int cLevers)
        {
            Boxes = cBoxes;
            Levers = cLevers;
        }


        public void WriteDeadends(string sPath)
        {
            if (!Directory.Exists(sPath))
            {
                Directory.CreateDirectory(sPath);
            }
            StreamWriter swProblem = new StreamWriter(sPath + "/dead.pddl");
            swProblem.WriteLine("(define (problem deadends_" + Name + ")");
            swProblem.WriteLine("  (:domain " + Name + ")");
            swProblem.WriteLine("(:init ");
            for (int i = 1; i <= Boxes; i++)
            {
                swProblem.WriteLine("   (and (gold-in box" + i + ") (not-controlled box" + i + "))");

            }
            swProblem.WriteLine("))");
            swProblem.Close();
        }

        public void WriteProblem(string sPath)
        {
            if (!Directory.Exists(sPath))
            {
                Directory.CreateDirectory(sPath);
            }
            StreamWriter swProblem = new StreamWriter(sPath + "/p.pddl");
            swProblem.WriteLine("(define (problem " + Name + ")");
            swProblem.WriteLine("  (:domain " + Name + ")");

            swProblem.WriteLine("(:init ");
            for (int i = 1; i <= Levers; i++)
            {
                swProblem.Write("   (oneof");
                for (int j = 1; j <= Boxes; j++)
                    swProblem.Write(" (controls lev" + i + " box" + j + ")");
                swProblem.WriteLine(")");
            }
            swProblem.WriteLine("");

            for (int i = 1; i <= Boxes; i++)
            {
                swProblem.Write("   (or");
                for (int j = 1; j <= Levers; j++)
                    swProblem.Write(" (controls lev" + j + " box" + i + ")");
                swProblem.WriteLine(" (not-controlled box" + i + "))");
            }
            swProblem.WriteLine("");

            for (int i = 1; i <= Boxes; i++)
            {
                for (int j = 1; j <= Levers; j++)
                    swProblem.WriteLine("   (or (not (controls lev" + j + " box" + i + ")) (not (not-controlled box" + i + ")))");
            }
            swProblem.WriteLine("");

            swProblem.Write("   (oneof");
            for (int i = 1; i <= Boxes; i++)
            {
                swProblem.Write(" (gold-in box" + i + ")");
            }
            swProblem.WriteLine("   )");
            swProblem.WriteLine(")");


            swProblem.WriteLine(" (:goal (and (has-gold)  ) )");
            swProblem.WriteLine(")");

            swProblem.Close();
        }

        public void WriteDomain(string sPath)
        {
            if (!Directory.Exists(sPath))
            {
                Directory.CreateDirectory(sPath);
            }
            StreamWriter swDomain = new StreamWriter(sPath + "/d.pddl");
            swDomain.WriteLine("(define (domain " + Name + ")");
            swDomain.WriteLine("  (:types box lever)");

            swDomain.WriteLine("  (:constants");
            for (int i = 1; i <= Boxes; i++)
                swDomain.Write("box" + i + " ");
            swDomain.WriteLine(" - box");
            for (int i = 1; i <= Levers; i++)
                swDomain.Write("lev" + i + " ");
            swDomain.WriteLine(" - lever");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");

            swDomain.WriteLine("    (:predicates 	(controls ?b - lever ?i - box)");
            swDomain.WriteLine("				(opened ?i - box)");
            swDomain.WriteLine("				(not-controlled ?i - box)");
            swDomain.WriteLine("                (gold-in ?j - box) (has-gold)");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action is_opened");
            swDomain.WriteLine("   :parameters (?i - box )");
            swDomain.WriteLine("   :observe (opened ?i))");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action look_in_box");
            swDomain.WriteLine("   :parameters (?i - box )");
            swDomain.WriteLine("   :precondition (opened ?i)");
            swDomain.WriteLine("   :observe (gold-in ?i))");
            swDomain.WriteLine("");


            swDomain.WriteLine("  (:action take_gold");
            swDomain.WriteLine("   :parameters (?i - box )");
            swDomain.WriteLine("   :precondition (and (opened ?i) (gold-in ?i))");
            swDomain.WriteLine("   :effect (has-gold))");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action push");
            swDomain.WriteLine("   :parameters (?i - lever)");
            swDomain.WriteLine("    :effect (and ");
            for (int i = 1; i <= Boxes; i++)
                swDomain.WriteLine("        (when (controls ?i box" + i + ") (opened box" + i + "))");
            swDomain.WriteLine("        )");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action pull");
            swDomain.WriteLine("   :parameters (?i - lever)");
            swDomain.WriteLine("    :effect (and ");
            for (int i = 1; i <= Boxes; i++)
                swDomain.WriteLine("        (when (controls ?i box" + i + ") (not (opened box" + i + ")))");
            swDomain.WriteLine("        )");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");


            swDomain.WriteLine(")");

            swDomain.Close();
        }

    }
}
