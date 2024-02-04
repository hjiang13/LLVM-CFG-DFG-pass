#include"graph.h"

using namespace llvm;
namespace {

	struct DFGPass : public ModulePass {
	public:
		static char ID;
		map<string, Graph*> DFGs;
		map<string, Graph*> CFGs;

		DFGPass() : ModulePass(ID) {}

		bool runOnModule(Module &M) override {
			errs() << "Hailong: Run on Module" << "\n" ;
			for (Module::iterator iter_F = M.begin(), FEnd = M.end(); iter_F != FEnd; ++iter_F) {
				errs() << "Hailong: interating through Modules \n";
				Function *F = &*iter_F;
				Graph* control_flow_G = new Graph(F);
				Graph* data_flow_G = new Graph(F);
				// F->viewCFG();
				errs() << "Hailong: F->getName().str(): " << F->getName().str() << " \n";
				DFGs.insert(pair<string, Graph*>(F->getName().str(), data_flow_G));
				CFGs.insert(pair<string, Graph*>(F->getName().str(), control_flow_G));
				//This is counfusing, let's iterate through the map to see what is inside the map
				for (auto i = DFGs.begin(); i != DFGs.end(); i++){
					errs() << i->first << " \t\t\t " << i->second << "\n";
				}
				control_flow_G->head.push_back(pair<Value*, Value*>(&*(F->begin())->begin(), &*(F->begin())->begin()));
				for (Function::iterator BB = F->begin(), BEnd = F->end(); BB != BEnd; ++BB) {
					errs() << "Hailong: interating through Function \n";
					BasicBlock *curBB = &*BB;
					for (BasicBlock::iterator II = curBB->begin(), IEnd = curBB->end(); II != IEnd; ++II) {
						Instruction* curII = &*II;
						errs() << "Hailong: interating through Basic Block \n";
						switch (curII->getOpcode())
						{
							// for the case of load operation, we should save the value of it
							case llvm::Instruction::Load:
							{
								errs() << "Hailong: Case of Load instruction \n";
								LoadInst* linst = dyn_cast<LoadInst>(curII);
								Value* loadValPtr = linst->getPointerOperand();
								insert(data_flow_G, pair<Value*, Value*>(loadValPtr, curII));
								break;
							}
							// for the case of store operation, both of the pointer and value should be recoded
							case llvm::Instruction::Store: {
								errs() << "Hailong: Case of Store instruction \n";
								StoreInst* sinst = dyn_cast<StoreInst>(curII);
								Value* storeValPtr = sinst->getPointerOperand();
								Value* storeVal = sinst->getValueOperand();
								insert(data_flow_G, pair<Value*, Value*>(storeVal, curII));
								insert(data_flow_G, pair<Value*, Value*>(curII, storeValPtr));
								data_flow_G->head.push_back(pair<Value*, Value*>(storeValPtr, storeVal));
								break;
							}

							case llvm::Instruction::Call: {
								errs() << "Hailong: Case of Call instruction \n";
								CallInst* cinst = dyn_cast<CallInst>(curII);
								errs() << "Hailong: instruction is : " << *cinst <<"\n";
								string f_name = std::string(cinst->getCalledFunction()->getName());
								errs() << "Hailong: f_name is : " << f_name <<"\n";
								//auto it = DFGs.find(f_name);
								//errs()<< "Hailong: we can find function " << it->first << " = " << it->second << "\n";
								//errs() << "Hailong: DFGs[f_name] is " << DFGs[f_name] << "\n";
								//This is counfusing, let's iterate through the map to see what is inside the map
								for (auto i = DFGs.begin(); i != DFGs.end(); i++){
									errs() << i->first << " \t\t\t " << i->second << "\n";
									//errs() << typeid(i->second).name() << "\n";
								}
								if ( DFGs.find(f_name) != DFGs.end() ){
									errs() <<"Hailong: DFGs is looking for the " << f_name << "\n";
									for(auto iter = DFGs[f_name]->F->arg_begin(), iter_end = DFGs[f_name]->F->arg_end(); iter != iter_end; iter++){
										errs() << "Hailong: iter is : " << iter <<"\n";
										data_flow_G->link.push_back(pair<Value*, Value*>(cinst, iter));
										errs()<<*cinst<<cinst<<"->"<<*iter<<iter<<"\n";
										// insert(data_flow_G, pair<Value*, Value*>(cinst, iter));
									}
									if(!DFGs[f_name]->F->doesNotReturn()){
										Value* ret_i = &*(--(--DFGs[f_name]->F->end())->end());
										data_flow_G->link.push_back(pair<Value*, Value*>(ret_i, cinst));
									// insert(data_flow_G, pair<Value*, Value*>(ret_i, cinst));
									}
								}

							}
							// for other operation, we get all the operand point to the current instruction
							default: {
								for (Instruction::op_iterator op = curII->op_begin(), opEnd = curII->op_end(); op != opEnd; ++op)
								{
									Instruction* tempIns;
									if (dyn_cast<Instruction>(*op))
									{
										insert(data_flow_G, pair<Value*, Value*>(op->get(), curII));
									}
								}
								break;
							}
						}
						BasicBlock::iterator next = II;
						++next;
						if (next != IEnd) {
							insert(control_flow_G, pair<Value*, Value*>(curII, &*next));
						}
					}

					Instruction* terminator = curBB->getTerminator();
					for (BasicBlock* sucBB : successors(curBB)) {
						Instruction* first = &*(sucBB->begin());
						insert(control_flow_G, pair<Value*, Value*>(terminator, first));
					}
				}
				
				
				writeFileByGraph(F);
				 
				
			}

			// NOTWITHCFHG indicate the fianl graph represents no CFG information
			writeFileByGraphGloble(NOTWITHCFG);
			errs()<<"end\n";
			return false;
		}

		void DFS_plot(Edge* v, Graph* G, raw_fd_ostream& file)
		{
			errs() << "Hailong: Function DFS_plot \n";
			Edge* p = v;
			while (p)
			{
				if (mark.find(pair<int, int>(p->v_from, p->v_to)) == mark.end()) 
				{
					mark.insert(pair<int, int>(p->v_from, p->v_to));
					file << "\tNode" << G->v[p->v_from]->va << " -> Node" << G->v[p->v_to]->va << "\n";
					DFS_plot(G->v[p->v_to]->first_out, G, file);
				}
				p = p->out_edge;
			}
			errs() << "Hailong: Function DFS_plot completed \n";
		}

		void writeFileByGraph(Function *F){
			errs() << "Hailong: Function writeFileByGraph \n";
			std::error_code error;
			enum sys::fs::OpenFlags F_None;
			string fileName(F->getName().str() + ".dot");
			raw_fd_ostream file(fileName, error, F_None);
			Graph* data_flow_G =  DFGs[F->getName().str()];
			Graph* control_flow_G = CFGs[F->getName().str()];

			file << "digraph \"DFG for'" + F->getName() + "\' function\" {\n";
			errs() << "Hailong: writing digraph \"DFG for' " + F->getName() + " \n";
			//Before interate the vector -- DFGs[F->getName().str()]->v, we need to check if the vector is empty,which leads to segmentation fault. 
			if (DFGs[F->getName().str()]->v.empty()){
				return;
			}
			for (auto node_iter = DFGs[F->getName().str()]->v.begin(), node_end = DFGs[F->getName().str()]->v.end(); node_iter != node_end; ++node_iter) 
			{
				errs() << "Hailong: DFGs[F->getName().str()]->v.begin(): " << *node_iter << " \n";
				Value* p = (*node_iter)->va;
				if(isa<Instruction>(*p))
				{
					file << "\tNode" << p << "[shape=record, label=\"" << *p << "\"];\n";
				}
				else
				{
					file << "\tNode" << p << "[shape=ellipse, label=\"" << *p << "\\l" << p << "\"];\n";
				}
			}
			// plot the instruction flow edge
			mark.clear();
			for(auto iter = control_flow_G->head.begin(), iter_end = control_flow_G->head.end(); iter != iter_end; iter++){
				DFS_plot(control_flow_G->v[find(control_flow_G->v, iter->second)]->first_out, control_flow_G, file);
			}
			errs() << "Hailong: plot the instruction flow edge compeleted" << "\n";
			// plot the data flow edge
			file << "edge [color=red]" << "\n";
			mark.clear();
			for(auto iter = data_flow_G->head.begin(), iter_end = data_flow_G->head.end(); iter != iter_end; iter++){
				DFS_plot(data_flow_G->v[find(data_flow_G->v, iter->second)]->first_out, data_flow_G, file);
			}
			errs() << "Hailong: plot the data flow edge compeleted" << "\n";
			file << "}\n";
			file.close();
		}

		void writeFileByGraphGloble(Mode m){
			errs() << "Hailong: Function writeFileByGraphGloble \n";
			std::error_code error;
			enum sys::fs::OpenFlags F_None;
			string fileName("all.dot");
			raw_fd_ostream file(fileName, error, F_None);

			file << "digraph \"DFG for all\" {\n";
			for(auto F_iter = DFGs.begin(), F_iter_end = DFGs.end(); F_iter != F_iter_end; F_iter++){
				errs() << "Hailong: F_iter->first is " << F_iter->first <<" \n";
				//if (F_iter->first == "printf"){
				//	continue; // To skip the system functions
				//}
				Graph* data_flow_G =  DFGs[F_iter->first];
				Graph* control_flow_G = CFGs[F_iter->first];
				auto nodes = F_iter->second->v;
				
				for (auto node_iter = nodes.begin(), node_end =  nodes.end(); node_iter != node_end; ++node_iter) 
				{
					Value* p = (*node_iter)->va;
					errs() << "Hailong: (*node_iter)->va " << (*node_iter)->va <<" \n";
					if(isa<Instruction>(*p))
					{
						file << "\tNode" << p << "[shape=record, label=\"" << *p << "\"];\n";
					}
					else
					{
						file << "\tNode" << p << "[shape=ellipse, label=\"" << *p << "\\l" << p << "\"];\n";
					}
				}
				// plot the instruction flow edge
				if(m != NOTWITHCFG){
					file << "edge [color=black]" << "\n";
					mark.clear();
					errs() << "Hailong: Iteration through control_flow_G->head begin." << "\n";
					for(auto iter = control_flow_G->head.begin(), iter_end = control_flow_G->head.end(); iter != iter_end; iter++){
						DFS_plot(control_flow_G->v[find(control_flow_G->v, iter->second)]->first_out, control_flow_G, file);
					}
					errs() << "Hailong: Iteration through control_flow_G->head completed." << "\n";
				}

				// plot the data flow edge
				vector<string> color_set = {"red", "blue", "cyan", "orange", "yellow", "green", "purple"};
				mark.clear();
				int count = 0;
				errs() << "Hailong: Iteration through data_flow_G->head begin." << "\n";
				for(auto iter = data_flow_G->head.begin(), iter_end = data_flow_G->head.end(); iter != iter_end; iter++){
					if (count > 6){
						count = 0;
					} // To stop index overstacking the color set
					file << "edge [color=" << color_set[count++] << "]" << "\n";
					DFS_plot(data_flow_G->v[find(data_flow_G->v, iter->second)]->first_out, data_flow_G, file);
				}
				errs() << "Hailong: Iteration through data_flow_G->head completed." << "\n";
				for(auto iter = data_flow_G->link.begin(), iter_end = data_flow_G->link.end(); iter != iter_end; iter++){
					file << "edge [color=grey]" << "\n";
					file << "\tNode" << iter->first << " -> Node" << iter->second << "\n";
					errs()<<"Hailong: *iter->first:" << iter->first << " and *iter->second:"<< iter->second << "\n";
				}
			}
			file << "}\n";
			file.close();
		}

	};
}

char DFGPass::ID = 0;
static RegisterPass<DFGPass> X("DFGPass", "DFG Pass Analyse",
	false, false
);