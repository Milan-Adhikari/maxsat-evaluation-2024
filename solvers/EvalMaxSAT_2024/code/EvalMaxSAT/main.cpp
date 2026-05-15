#include <iostream>
#include <cassert>
#include <csignal>
#include <chrono>

#include <unistd.h>
#include <sys/types.h>
#include <signal.h>
#include <sys/wait.h>
#include <memory>

#include "EvalMaxSAT.h"
#include "lib/CLI11.hpp"

using namespace MaLib;

Chrono TotalChrono("c Total time");
std::string PATH_ANYTIME_SOLVER = "./nuwls";

std::string exec(std::string cmd) {
    std::array<char, 128> buffer;
    std::string result;
    std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(cmd.c_str(), "r"), pclose);
    if (!pipe) {
        throw std::runtime_error("popen() failed!");
    }
    while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
        result += buffer.data();
    }
    return result;
}

std::tuple<bool, t_weight, std::vector<bool>> getUB(std::string file, unsigned int timeout, std::string path) {
    std::vector<bool> values;
    t_weight weight = std::numeric_limits<t_weight>::max();

    std::string result = exec(toString("timeout -s 15 ",timeout," timeout -s 9 ", timeout+10, " ", path, " ", file, " 2> /dev/null"));
    std::istringstream issResult(result);

    std::string line;
    std::string res;
    bool satisfiable = false;
    while (std::getline(issResult, line))
    {
        std::istringstream iss(line);
        char action;
        if(!(iss >> action)) {
            continue;
        }
        switch (action) {

        case 'c':
        {
            break;
        }

        case 'o':
        {
            if(!(iss >> weight)) {
                assert(false);
            }
            break;
        }

        case 's':
        {
            if(!(iss >> res)) {
                assert(false);
            }
            if( (res.compare("SATISFIABLE") == 0) ) {
                satisfiable = true;
            }
            if( (res.compare("OPTIMUM") == 0) ) {
                satisfiable = true;
            }
            break;
        }

        case 'v':
        {
            if(!(iss >> res)) {
                assert(false);
            }
            values.push_back(0); // fake lit

            int res2;
            if(!(iss >> res2)) {
                if(res.compare("-1") ==  0) {
                    res = "0"; // special case of a single variable
                }

                // New format
                for(unsigned int i=0; i<res.size(); i++) {
                    values.push_back(res[i] == '1');
                }
            } else {
                // Old format
                int lit = std::atoi(res.c_str());
                values.push_back(lit > 0);
                assert((values.size()-1) == abs(lit));

                values.push_back(res2 > 0);

                while(iss>>lit) {
                    values.push_back(lit > 0);
                    assert((values.size()-1) == abs(lit));
                }
            }

            break;
        }

        default:
            assert(false);
        }
    }

    return {satisfiable, weight, values};
}


std::string cur_file;
std::unique_ptr<EvalMaxSAT<Solver_cadical>> monMaxSat;
bool oldOutputFormat = false;
bool bench = false;

void signalHandler( int signum ) {
    std::cout << "c Interrupt signal (" << signum << ") received."<< std::endl;

    if(monMaxSat != nullptr) {
        auto solution = monMaxSat->getSolution();
        if(bench) {
                std::cout << cur_file << "\t" << calculateCost(cur_file, solution) << "\t" << TotalChrono.tacSec() << std::endl;
        } else {
            t_weight cost = calculateCost(cur_file, solution);

            if(cost != -1) {
                if(oldOutputFormat) {
                    std::cout << "o " << calculateCost(cur_file, solution) << std::endl;
                    std::cout << "s SATISFIABLE" << std::endl;
                    std::cout << "v";
                    for(unsigned int i=1; i<solution.size(); i++) {
                        if(solution[i]) {
                            std::cout << " " << i;
                        } else {
                            std::cout << " -" << i;
                        }
                    }
                    std::cout << std::endl;
                } else {
                    std::cout << "o " << calculateCost(cur_file, solution) << std::endl;
                    std::cout << "s SATISFIABLE" << std::endl;
                    //std::cout << "o " << calculateCost(file, solution) << std::endl;
                    std::cout << "v ";
                    for(unsigned int i=1; i<solution.size(); i++) {
                        std::cout << solution[i];
                    }
                    std::cout << std::endl;
                }
                exit(10); // The solver finds a solution satisfying the hard clauses but does not prove it to be optimal
            } else {
                std::cout << "s UNKNOWN" << std::endl;
                exit(0); // The solver cannot find a solution satisfying the hard clauses or prove unsatisfiability
            }
        }
    }

    exit(0); // Bench mode
}


template<class SOLVER>
std::tuple<bool, std::vector<bool>, t_weight> solveFile(SOLVER *monMaxSat, std::string file, double targetComputationTime=3600, double timeForSCIP=500, double timeForUB=120, bool simplify = true) {
    cur_file = file;


    std::cout << "c targetComputationTime = " << targetComputationTime << std::endl;
    unsigned int timeOutSimplify = max((unsigned int) 1, (unsigned int)(0.05*targetComputationTime));

    if(simplify) {
        if(!parse_and_simplify(file, monMaxSat, timeOutSimplify, 0.3, 1) ) {
            std::cerr << "Unable to read the file " << file << std::endl;
            assert(false);
            return std::make_tuple<bool, std::vector<bool>, t_weight>(false, {},-1);
        }
        MonPrint("c Fin parse and simplification in ", TotalChrono.tacSec(), "s");
    } else {
        if(!parse(file, monMaxSat)) {
            std::cerr << "Unable to read the file " << file << std::endl;
            assert(false);
            return std::make_tuple<bool, std::vector<bool>, t_weight>(false, {},-1);
        }
    }


    if(timeForUB>0) {
        if( (monMaxSat->nClauses() > 200) && (monMaxSat->nVars() > 20) ) {
            auto [sat, solCost, sol] = getUB(file, timeForUB, PATH_ANYTIME_SOLVER);
            if(sat && sol.size()) {
                if(solCost < monMaxSat->getCost()) {
                    MonPrint("c Upper bound = ", solCost);
                    std::cout << "o " << solCost << std::endl;
                    monMaxSat->setSolution(sol, solCost);
                }
            }
        }
    }

    
    monMaxSat->setTargetComputationTime( targetComputationTime - TotalChrono.tacSec(), timeForSCIP );
    if(monMaxSat->isWeighted() == false) {
        monMaxSat->disableOptimize();
    }
    if(!monMaxSat->solve()) {
        //std::cout << "s UNSATISFIABLE" << std::endl;
        return std::make_tuple<bool, std::vector<bool>, t_weight>(false, {},-1);
    }
    auto solution = monMaxSat->getSolution();
    std::cout << "c nombre de var = " << solution.size() << std::endl;
    assert(monMaxSat->getCost() == calculateCost(file, solution));
    if(monMaxSat->getCost() != calculateCost(file, solution)) {
        std::cout << "c Err ?" << std::endl;
    }

    return {true, solution, calculateCost(file, solution)};
}

int main(int argc, char *argv[])
{
    assert([](){std::cout << "c Assertion activated. For better performance, compile the project with assertions disabled. (-DNDEBUG)" << std::endl; return true;}());

    signal(SIGINT, signalHandler);
    signal(SIGTERM, signalHandler);

    ///////////////////////////
    /// PARSE ARG
    ///
        CLI::App app{"EvalMaxSAT Solver"};

        std::string file;
        app.add_option("file", file, "File with the formula to be solved (wcnf format)")->check(CLI::ExistingFile)->required();

        unsigned int minimalRefTime=1;
        app.add_option("--minRefTime", minimalRefTime, toString("Minimal reference time to improve unsat core (default = ",minimalRefTime,")"));

        unsigned int maximalRefTime=5*60;
        app.add_option("--maxRefTime", maximalRefTime, toString("Maximal reference time to improve unsat core (default = ",maximalRefTime,")"));

        unsigned int targetComputationTime = 60*60;
        app.add_option("--TCT", targetComputationTime, toString("Target Computation Time (default = ",targetComputationTime,")"));

        double coefOnRefTime = 1.66;
        app.add_option("--coefAVG", coefOnRefTime, toString("Average coef on ref time (default = ",coefOnRefTime,")"));

        double initialCoef = 10;
        app.add_option("--coefInit", initialCoef, toString("Initial coef on ref time (default = ",initialCoef,")"));

        app.add_flag("--old", oldOutputFormat, "Use old output format");

        unsigned int timeForUB = 60*3;
        app.add_option("--timeUB", timeForUB, toString("Time in seconds for the calculation of an upper bound (default: ",timeForUB,")"));

        app.add_option("--path_anytime_solver", PATH_ANYTIME_SOLVER, toString("Path to the anytime solver (default: ",PATH_ANYTIME_SOLVER,")"))->check(CLI::ExistingFile);

        app.add_flag("--bench", bench, "Bench mode");

        bool noDS=false;
        app.add_flag("--noDS", noDS, "Unactivate Delay Strategy");

        bool noMS=false;
        app.add_flag("--noMS", noMS, "Unactivate Multisolve Strategy");

        bool noUBS=false;
        app.add_flag("--noUBS", noUBS, "Unactivate UB Strategy");

        unsigned int timeForSCIP = 400;
        app.add_option("--timeSCIP", timeForSCIP, toString("Time in seconds for SCIP (default: ",timeForSCIP,")"));

        long long expectedCost = -1;
        app.add_option("--expectedCost", expectedCost, "Expected cost");

        bool unactivated_simplify = false;
        app.add_flag("--noSimplify", unactivated_simplify, "Unactivate simplification");

        bool no_save_cores = false;
        app.add_flag("--noSaveCores", no_save_cores, "Unactivate saving cores");

        CLI11_PARSE(app, argc, argv);
    ///
    ////////////////////////////////////////

    monMaxSat = std::make_unique<EvalMaxSAT<Solver_cadical>>();
    monMaxSat->setCoef(initialCoef, coefOnRefTime);
    monMaxSat->setBoundRefTime(minimalRefTime, maximalRefTime);
    monMaxSat->setSaveCores(!no_save_cores);

    if(noDS) {
        monMaxSat->unactivateDelayStrategy();
    }
    if(noMS) {
        monMaxSat->unactivateMultiSolveStrategy();
    }
    if(noUBS) {
        monMaxSat->unactivateUBStrategy();
    }

    auto [sat, solution, cost] = solveFile(monMaxSat.get(), file, targetComputationTime, timeForSCIP, timeForUB, !unactivated_simplify);

    if(bench) {
        std::cout << file << "\t" << calculateCost(file, solution) << "\t" << TotalChrono.tacSec() << std::endl;
        if(expectedCost != cost) {
            std::cerr << "Expected cost: " << expectedCost << " but found: " << cost << std::endl;
            return 1;
        }
        if(cost != calculateCost(file, solution)) {
            std::cerr << "Cost is not the same as the one calculated" << std::endl;
            return 2;
        }
    } else {
        if(sat) {
            if(oldOutputFormat) {
                ////// PRINT SOLUTION OLD FORMAT //////////////////
                ///
                    std::cout << "o " << calculateCost(file, solution) << std::endl;
                    std::cout << "s OPTIMUM FOUND" << std::endl;
                    std::cout << "v";
                    for(unsigned int i=1; i<solution.size(); i++) {
                        if(solution[i]) {
                            std::cout << " " << i;
                        } else {
                            std::cout << " -" << i;
                        }
                    }
                    std::cout << std::endl;
                ///
                ///////////////////////////////////////
            } else {
                ////// PRINT SOLUTION NEW FORMAT //////////////////
                ///
                    std::cout << "o " << calculateCost(file, solution) << std::endl;
                    std::cout << "s OPTIMUM FOUND" << std::endl;
                    std::cout << "v ";
                    for(unsigned int i=1; i<solution.size(); i++) {
                        std::cout << solution[i];
                    }
                    std::cout << std::endl;
                ///
                ///////////////////////////////////////
            }
            return 30; // OPT
        } else {
            std::cout << "s UNSATISFIABLE" << std::endl;
            return 20; // UNSAT
        }
    }

    assert(calculateCost(file, solution) == cost);

    return 0; // Bench mode
}





