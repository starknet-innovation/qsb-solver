__global__ void compare(uint32_t *a,uint32_t *b,const uint32_t *input,int n){
 int i=blockIdx.x*blockDim.x+threadIdx.x;if(i>=n)return;
 uint32_t x[8],y[8];for(int j=0;j<8;j++)x[j]=y[j]=input[i*8+j];
 for(int k=0;k<17;k++){
  baseline::qsb_compress_generic_tail(x,k);candidate::qsb_compress_generic_tail(y,k);
  for(int j=0;j<8;j++){a[(i*17+k)*8+j]=x[j];b[(i*17+k)*8+j]=y[j];}
 }
}
void reference(uint32_t *s,const uint32_t *w){
 uint32_t v[8];memcpy(v,s,32);
 for(int i=0;i<64;i++){
  uint32_t t=v[7]+S1(v[4])+Ch(v[4],v[5],v[6])+w[i];
  uint32_t u=S0(v[0])+Maj(v[0],v[1],v[2]);
  for(int j=7;j>0;j--)v[j]=v[j-1];v[4]+=t;v[0]=t+u;
 }
 for(int j=0;j<8;j++)s[j]+=v[j];
}
int main(){
 const int n=1024;size_t bytes=n*17*8*sizeof(uint32_t);
 std::vector<uint32_t> states(n*8),w(17*64),a(n*17*8),b(n*17*8);
 std::mt19937 rng(20260930);for(auto &x:states)x=rng();
 uint32_t *ds,*dw,*da,*db;CK(cudaMalloc(&ds,states.size()*4));CK(cudaMalloc(&dw,w.size()*4));
 CK(cudaMalloc(&da,bytes));CK(cudaMalloc(&db,bytes));
 CK(cudaMemcpy(ds,states.data(),states.size()*4,cudaMemcpyHostToDevice));
 CK(cudaMemcpyToSymbol(baseline::QSB_GENERIC_TAIL_SCHEDULE,&dw,sizeof(dw)));
 CK(cudaMemcpyToSymbol(candidate::QSB_GENERIC_TAIL_SCHEDULE,&dw,sizeof(dw)));
 unsigned checked=0;
 for(int trial=0;trial<10;trial++){
  for(auto &x:w)x=trial==0?0:trial==1?UINT32_MAX:rng();
  CK(cudaMemcpy(dw,w.data(),w.size()*4,cudaMemcpyHostToDevice));
  compare<<<(n+127)/128,128>>>(da,db,ds,n);CK(cudaGetLastError());CK(cudaDeviceSynchronize());
  CK(cudaMemcpy(a.data(),da,bytes,cudaMemcpyDeviceToHost));CK(cudaMemcpy(b.data(),db,bytes,cudaMemcpyDeviceToHost));
  for(int i=0;i<n;i++){
   uint32_t ref[8];memcpy(ref,states.data()+i*8,32);
   for(int k=0;k<17;k++){
    reference(ref,w.data()+k*64);size_t off=(i*17+k)*8;
    if(memcmp(ref,a.data()+off,32)||memcmp(ref,b.data()+off,32)){fprintf(stderr,"Mismatch %d %d %d\n",trial,i,k);return 3;}checked++;
   }
  }
 }
 CK(cudaFree(ds));CK(cudaFree(dw));CK(cudaFree(da));CK(cudaFree(db));
 printf("{\"status\":\"passed\",\"nativeCompressionComparisons\":%u,\"scope\":\"extracted compression only\"}\n",checked);
}
