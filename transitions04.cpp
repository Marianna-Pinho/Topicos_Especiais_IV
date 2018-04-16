#include <bits/stdc++.h>
#include "cudd-3.0.0/util/util.h"
#include "cudd-3.0.0/cudd/cudd.h"

 
using namespace std;

DdManager *gbm;
vector<string> names;
map<string, DdNode*> prop;
map<string, DdNode*> states;
map<string, DdNode*> transitions;

 
string removeSpaces(string input) {
  input.erase(std::remove(input.begin(),input.end(),' '),input.end());
  return input;
 
}
 
//Faz o split. Salva em um vetor pedaços de uma linha divididos por um char especifico.
const vector<string> splits(const string &s, const char &c)
{
    string buff{""};
 
    vector<string> v;
 
    for(auto n:s) {
        if((n != c) && (n != '(') && (n != ')')) {
            buff+=n;
        }
        else if(n == c && buff != "") {
            v.push_back(removeSpaces(buff));
            buff = "";
        }
    }
 
    if(buff != "") {
        v.push_back(removeSpaces(buff));
    }
 
    return v;
}
 
 
void print_dd (DdManager *gbm, DdNode *dd, int n, int pr )
{
    printf("DdManager nodes: %ld |\n ", Cudd_ReadNodeCount(gbm)); /*Reports the number of live nodes in BDDs and ADDs*/
    printf("DdManager vars: %d |\n ", Cudd_ReadSize(gbm) ); /*Returns the number of BDD variables in existence*/
    printf("DdManager reorderings: %d |\n ", Cudd_ReadReorderings(gbm) ); /*Returns the number of times reordering has occurred*/
    printf("DdManager memory: %ld \n", Cudd_ReadMemoryInUse(gbm) ); /*Returns the memory in use by the manager measured in bytes*/
    Cudd_PrintDebug(gbm, dd, n, pr);  // Prints to the standard output a DD and its statistics: number of nodes, number of leaves, number of minterms.
}
 
void write_dd (DdManager *gbm, DdNode *dd, char* filename)
{
    FILE *outfile; // output file pointer for .dot file
    outfile = fopen(filename,"w");
    if(outfile == NULL){
      printf("File didn't open\n");
      return;
    }
    DdNode **ddnodearray = (DdNode**)malloc(sizeof(DdNode*)); // initialize the function array
    ddnodearray[0] = dd;
    Cudd_DumpDot(gbm, 1, ddnodearray, NULL, NULL, outfile); // dump the function to .dot file
    free(ddnodearray);
    fclose (outfile); // close the file */
}
 
vector<string> createPropositions() {
    string line = "";
    ifstream file;
    vector<string>names;
    int i = 0, count  = 0;
 
   file.open("modelo.txt",ios::in | ios::binary); // abre o arquivo: Obs(segundo e terceiro parametros são um misterio).
 
 
    if (file.is_open()){
        while(line.compare("<propositions>") != 0 ) {
           getline(file,line);
        }
    }
    getline(file, line);
 
    while(line.compare("<\\propositions>") != 0 ) {
 
        vector<string> props{splits(line, ',')};
 
        for(i = 0; i < props.size(); i++){
            names.push_back(props[i]);
            names.push_back(props[i].append("'"));
            
            prop[names[count]] = Cudd_bddIthVar(gbm,count);
            Cudd_Ref(prop[names[count]]);
            prop[names[count+1]] = Cudd_bddIthVar(gbm,count+1);
            Cudd_Ref(prop[names[count+1]]);

            if(!Cudd_bddSetPairIndex(gbm, i, i+1)){
               printf("Pair didn't set \n");
           }
           count += 2;
        }

        getline(file, line);
    }

    file.close();
    return names;
  
}
 
string getWord(string word, char key){
    string nword = "";
 
    for(auto l: word){
        if(l != key){
            nword+=l;
        }else{
            break;
        }
    }
    return nword;
}
 
vector <string> compara(vector<string> propositions, vector<string> stateProps){
    int i = 0, j = 0;
    vector<string> notStates;

      for(j = 0; j < propositions.size(); j+=2){ //p,p',q,q',r,r',s,s'
          for(i = 0; i < stateProps.size(); i++){         //p,q,r,s
              if(propositions[j] == stateProps[i]){
                  propositions[j] = "-1";
              }
          }
        }

      for(i = 0; i < propositions.size();i+=2){
          if(propositions[i] != "-1"){
              notStates.push_back(propositions[i]);     
             }
      }
      return notStates;  

}
void createStates(vector<string>names) {
    string line; ifstream file;
    int i = 0, j = 0;
    DdNode * aux;

    file.open("modelo.txt",ios::in | ios::binary);
 
    if (file.is_open()) {
        while(line.compare("<states>") != 0 ) {
            getline(file, line);
        }
    }
 
    getline(file, line);
 
    while (line.compare("<\\states>") != 0) {
        j = 0;
        string nomeState = getWord(line, ':');
 
        vector<string> ps{splits(line.substr(nomeState.size()+1,line.length()-1), ',')};
        vector<string> notStates = compara(names, ps);

        // cout << "ps" << j << endl;
        // for(auto p: ps){
        //   cout << p << endl;
        // }

        // cout << "not"<< j << endl;
        // for(auto n: notStates){
        //   cout << n << endl;
        // }

        
        if(ps.size()!=0){
          aux = prop[ps[0]];
        }else{
          aux = Cudd_Not(prop[notStates[0]]);
        }

        for(i = 0; i < ps.size(); i++){
            states[nomeState] = Cudd_bddAnd(gbm, aux, prop[ps[i]]);
            Cudd_Ref(states[nomeState]);
            Cudd_RecursiveDeref(gbm,aux);
            aux = states[nomeState];
        }

        for(i = 0; i < notStates.size(); i++){
            states[nomeState] = Cudd_bddAnd(gbm, aux, Cudd_Not(prop[notStates[i]]));
            Cudd_Ref(states[nomeState]);
            Cudd_RecursiveDeref(gbm,aux);
            aux = states[nomeState];
        }
        Cudd_RecursiveDeref(gbm,aux);
       
         getline(file, line);
    }
 
    cout << "fim" << endl;
    file.close();
}

void createTransitions(int *permutation) {
    string line;
    ifstream file;

    file.open("modelo.txt",ios::in | ios::binary);
    if (file.is_open()) {
        while(line.compare("<transitions>") != 0 ) {
            getline(file, line);
        }
    }

    getline(file, line);
    while(line.compare("<\\transitions>") != 0 ) {
        vector<string> ps{splits(line, ',')};
        string trans = ps[0] + ps[1];

        transitions[trans] = Cudd_bddAnd(gbm, states[ps[0]], Cudd_bddPermute(gbm, states[ps[1]], permutation));
        Cudd_Ref(transitions[trans]);

      //  cout << trans << endl;
        //Update for the next line
        getline(file, line);
    }
}

char ** stringToChar(vector<string> words){
  int i = 0, j = 0;

  char *nomes[words.size()];

  for(i = 0; i < words.size(); i++){
      for(j = 0; words[i][j] != '\0'; j++){
        nomes[i][j] = words[i][j];
      }
        nomes[i][j] = '\0';
  }
}

int main(){
 
    char filename[100];
    gbm = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0);
    DdNode *Xdd,*Tdd, *print, *restrictBy, *restrictNot, *restrictF, *XTdd, *preFraca, *Xddl;
    int i = 0;
 
 /* ********** Creating Propositions ********* */
    names = createPropositions();

/* ************ Creating States ***************/
    createStates(names);

    map<string, DdNode*>::iterator it = states.begin();

    Xdd = states[it->first];
    for(map<string, DdNode*>::iterator it = states.begin(); it != states.end(); it++){
        Xdd = Cudd_bddOr(gbm, it->second, Xdd);
        Cudd_Ref(Xdd);       
    }

/* ********** Creating Transitions ********** */
    int permutation[prop.size()];

    for(i = 0; i < prop.size(); i+=2){
      permutation[i] = i+1;
      permutation[i+1] = i;
    }

    createTransitions(permutation);

    it = transitions.begin();
    Tdd = transitions[it->first];
    for(it = transitions.begin(); it != transitions.end(); it++){
        Tdd = Cudd_bddOr(gbm, it->second, Tdd);
        Cudd_Ref(Tdd);       
    }
   

/* ********************** Seting Pairs ****************** */
    // for(i = 0; i < (int)prop.size(); i++){
    //     if(!Cudd_bddSetPairIndex(gbm, i, i+1)){
    //         printf("Pair didn't set \n");
    //     }
    // }

/* ************************ Creating X'dd *************** */
    Xddl = Cudd_bddPermute(gbm, Xdd, permutation); 
       if(Xddl == NULL){
            printf("Permute failed\n");
       }

/* ******************* Applying EX ********************** */
    // aux = trans[0];
    // for (i = 0; i < 23; i++) {           //Fazendo o Ou entre todas as transições
    //     Tdd = Cudd_bddOr(gbm,trans[i+1],aux);
    //     Cudd_Ref(Tdd);
    //     Cudd_RecursiveDeref(gbm,aux);
    //     aux = Tdd;
    // }
    // Cudd_RecursiveDeref(gbm,aux);
    // DdNode *teste =  aux->second;
    XTdd = Cudd_bddAnd(gbm, Xddl, Tdd);
    i = 0;
    map<string, DdNode*>::iterator aux = prop.begin();
    aux++;
    restrictBy = aux->second;   //Fazemos isso para pegar o primeiro linha
    restrictNot = Cudd_Not(aux->second);
    restrictF = Cudd_bddOr(gbm, restrictBy, restrictNot);
    preFraca = XTdd;
    print = Cudd_BddToAdd(gbm,preFraca);
    print_dd(gbm, print, 8,4);
    for(map<string, DdNode*>::iterator it = prop.begin(); it != prop.end(); it++){ //Fazendo a AND entre todos os linha
        if((i%2)){  //Se i for uma posição ímpar, que é onde estão os linha
            // restrictBy = it->second;
            // preFraca = Cudd_bddRestrict(gbm, preFraca, restrictBy);
            // print = Cudd_BddToAdd(gbm,preFraca);
            // print_dd(gbm, print, 8,4);
            // cout << "\n" << endl;
          // restrictBy = Cudd_bddAnd(gbm, restrictBy, it->second); 
          // Cudd_Ref(restrictBy);
            preFraca = Cudd_bddOr(gbm, Cudd_bddRestrict(gbm, preFraca, it->second), Cudd_bddRestrict(gbm, preFraca, Cudd_Not(it->second)));
            print = Cudd_BddToAdd(gbm,preFraca);
            print_dd(gbm, print, 8,4);
            cout << "\n" << endl;
        }
        i++;
    }
        
    // XTdd = or(restrict(XTdd, it->second), restrict(XTdd, not(it->second)))
    // // DdNode *teste =  aux->second;
    //  XTdd = Cudd_bddAnd(gbm, Xddl, Tdd);
    //  preFraca = Cudd_bddRestrict(gbm, XTdd, restrictF);

     // DdNode *teste =  aux->second;
    // XTdd = Cudd_bddAnd(gbm, Xddl, Tdd);
    // preFraca = Cudd_bddRestrict(gbm, XTdd, teste);
    // aux++;
    // teste = aux->second;
    // DdNode *preFraca2 = Cudd_bddRestrict(gbm, XTdd, teste);

  /* **************** Saving Bdd *************** */
    // i = 0;
    // char *nome[prop.size()];
    // for(i = 0; i < prop.size(); i++){
    //     strcpy(nome[i],);
    // }
    print = Cudd_BddToAdd(gbm,preFraca);

    print_dd(gbm, print, 8,4);
    sprintf(filename, "bdd/graph.dot");
    write_dd(gbm, print, filename);
    Cudd_Quit(gbm);
 
     return 0;
}








