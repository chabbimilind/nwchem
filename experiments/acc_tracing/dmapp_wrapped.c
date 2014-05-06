
// GENERATED FILE DON'T EDIT
#include<dmapp.h>
#include<stdbool.h>
#include "barrier_deletion.h"
extern "C" {
#define REAL_FUNCTION(name)  __real_ ## name
#define WRAPPED_FUNCTION(name)  __wrap_ ## name
extern dmapp_return_t
 REAL_FUNCTION(dmapp_init) ( dmapp_rma_attrs_t *requested_attrs,
           dmapp_rma_attrs_t *actual_attrs) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_init) ( dmapp_rma_attrs_t *requested_attrs,
           dmapp_rma_attrs_t *actual_attrs) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_init)(requested_attrs, actual_attrs);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_init_ext) ( dmapp_rma_attrs_ext_t *requested_attrs,
               dmapp_rma_attrs_ext_t *actual_attrs) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_init_ext) ( dmapp_rma_attrs_ext_t *requested_attrs,
               dmapp_rma_attrs_ext_t *actual_attrs) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_init_ext)(requested_attrs, actual_attrs);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_finalize) (void) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_finalize) (void) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_finalize)();
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_set_rma_attrs) ( dmapp_rma_attrs_t *requested_attrs,
                    dmapp_rma_attrs_t *actual_attrs) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_set_rma_attrs) ( dmapp_rma_attrs_t *requested_attrs,
                    dmapp_rma_attrs_t *actual_attrs) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_set_rma_attrs)(requested_attrs, actual_attrs);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_set_rma_attrs_ext) ( dmapp_rma_attrs_ext_t *requested_attrs,
                        dmapp_rma_attrs_ext_t *actual_attrs) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_set_rma_attrs_ext) ( dmapp_rma_attrs_ext_t *requested_attrs,
                        dmapp_rma_attrs_ext_t *actual_attrs) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_set_rma_attrs_ext)(requested_attrs, actual_attrs);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_put_nb) ( void *target_addr,
             dmapp_seg_desc_t *target_seg,
             dmapp_pe_t target_pe,
             void *source_addr,
             uint64_t nelems,
             dmapp_type_t type,
             dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_put_nb) ( void *target_addr,
             dmapp_seg_desc_t *target_seg,
             dmapp_pe_t target_pe,
             void *source_addr,
             uint64_t nelems,
             dmapp_type_t type,
             dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_put_nb)(target_addr, target_seg, target_pe, source_addr, nelems, type, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_put_nbi) ( void *target_addr,
              dmapp_seg_desc_t *target_seg,
              dmapp_pe_t target_pe,
              void *source_addr,
              uint64_t nelems,
              dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_put_nbi) ( void *target_addr,
              dmapp_seg_desc_t *target_seg,
              dmapp_pe_t target_pe,
              void *source_addr,
              uint64_t nelems,
              dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_put_nbi)(target_addr, target_seg, target_pe, source_addr, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_put) ( void *target_addr,
          dmapp_seg_desc_t *target_seg,
          dmapp_pe_t target_pe,
          void *source_addr,
          uint64_t nelems,
          dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_put) ( void *target_addr,
          dmapp_seg_desc_t *target_seg,
          dmapp_pe_t target_pe,
          void *source_addr,
          uint64_t nelems,
          dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_put)(target_addr, target_seg, target_pe, source_addr, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_put_flag_nb) ( void *target_addr,
                  dmapp_seg_desc_t *target_seg,
                  dmapp_pe_t target_pe,
                  void *source_addr,
                  uint64_t nelems,
                  dmapp_type_t type,
                  void *target_flag,
                  uint64_t flag_value,
                  dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_put_flag_nb) ( void *target_addr,
                  dmapp_seg_desc_t *target_seg,
                  dmapp_pe_t target_pe,
                  void *source_addr,
                  uint64_t nelems,
                  dmapp_type_t type,
                  void *target_flag,
                  uint64_t flag_value,
                  dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_put_flag_nb)(target_addr, target_seg, target_pe, source_addr, nelems, type, target_flag, flag_value, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_put_flag_nbi) ( void *target_addr,
                   dmapp_seg_desc_t *target_seg,
                   dmapp_pe_t target_pe,
                   void *source_addr,
                   uint64_t nelems,
                   dmapp_type_t type,
                   void *target_flag,
                   uint64_t flag_value) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_put_flag_nbi) ( void *target_addr,
                   dmapp_seg_desc_t *target_seg,
                   dmapp_pe_t target_pe,
                   void *source_addr,
                   uint64_t nelems,
                   dmapp_type_t type,
                   void *target_flag,
                   uint64_t flag_value) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_put_flag_nbi)(target_addr, target_seg, target_pe, source_addr, nelems, type, target_flag, flag_value);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_put_flag) ( void *target_addr,
               dmapp_seg_desc_t *target_seg,
               dmapp_pe_t target_pe,
               void *source_addr,
               uint64_t nelems,
               dmapp_type_t type,
               void *target_flag,
               uint64_t flag_value) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_put_flag) ( void *target_addr,
               dmapp_seg_desc_t *target_seg,
               dmapp_pe_t target_pe,
               void *source_addr,
               uint64_t nelems,
               dmapp_type_t type,
               void *target_flag,
               uint64_t flag_value) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_put_flag)(target_addr, target_seg, target_pe, source_addr, nelems, type, target_flag, flag_value);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_get_nb) ( void *target_addr,
             void *source_addr,
             dmapp_seg_desc_t *source_seg,
             dmapp_pe_t source_pe,
             uint64_t nelems,
             dmapp_type_t type,
             dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_get_nb) ( void *target_addr,
             void *source_addr,
             dmapp_seg_desc_t *source_seg,
             dmapp_pe_t source_pe,
             uint64_t nelems,
             dmapp_type_t type,
             dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_get_nb)(target_addr, source_addr, source_seg, source_pe, nelems, type, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_get_nbi) ( void *target_addr,
              void *source_addr,
              dmapp_seg_desc_t *source_seg,
              dmapp_pe_t source_pe,
              uint64_t nelems,
              dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_get_nbi) ( void *target_addr,
              void *source_addr,
              dmapp_seg_desc_t *source_seg,
              dmapp_pe_t source_pe,
              uint64_t nelems,
              dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_get_nbi)(target_addr, source_addr, source_seg, source_pe, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_get) ( void *target_addr,
          void *source_addr,
          dmapp_seg_desc_t *source_seg,
          dmapp_pe_t source_pe,
          uint64_t nelems,
          dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_get) ( void *target_addr,
          void *source_addr,
          dmapp_seg_desc_t *source_seg,
          dmapp_pe_t source_pe,
          uint64_t nelems,
          dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_get)(target_addr, source_addr, source_seg, source_pe, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_get_flag_nbi) ( void *target_addr,
                   void *source_addr,
                   dmapp_seg_desc_t *source_seg,
                   dmapp_pe_t source_pe,
                   uint64_t nelems,
                   dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_get_flag_nbi) ( void *target_addr,
                   void *source_addr,
                   dmapp_seg_desc_t *source_seg,
                   dmapp_pe_t source_pe,
                   uint64_t nelems,
                   dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_get_flag_nbi)(target_addr, source_addr, source_seg, source_pe, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_iput_nb) ( void *target_addr,
              dmapp_seg_desc_t *target_seg,
              dmapp_pe_t target_pe,
              void *source_addr,
              ptrdiff_t tst,
              ptrdiff_t sst,
              uint64_t nelems,
              dmapp_type_t type,
              dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_iput_nb) ( void *target_addr,
              dmapp_seg_desc_t *target_seg,
              dmapp_pe_t target_pe,
              void *source_addr,
              ptrdiff_t tst,
              ptrdiff_t sst,
              uint64_t nelems,
              dmapp_type_t type,
              dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_iput_nb)(target_addr, target_seg, target_pe, source_addr, tst, sst, nelems, type, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_iput_nbi) ( void *target_addr,
               dmapp_seg_desc_t *target_seg,
               dmapp_pe_t target_pe,
               void *source_addr,
               ptrdiff_t tst,
               ptrdiff_t sst,
               uint64_t nelems,
               dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_iput_nbi) ( void *target_addr,
               dmapp_seg_desc_t *target_seg,
               dmapp_pe_t target_pe,
               void *source_addr,
               ptrdiff_t tst,
               ptrdiff_t sst,
               uint64_t nelems,
               dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_iput_nbi)(target_addr, target_seg, target_pe, source_addr, tst, sst, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_iput) ( void *target_addr,
           dmapp_seg_desc_t *target_seg,
           dmapp_pe_t target_pe,
           void *source_addr,
           ptrdiff_t tst,
           ptrdiff_t sst,
           uint64_t nelems,
           dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_iput) ( void *target_addr,
           dmapp_seg_desc_t *target_seg,
           dmapp_pe_t target_pe,
           void *source_addr,
           ptrdiff_t tst,
           ptrdiff_t sst,
           uint64_t nelems,
           dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_iput)(target_addr, target_seg, target_pe, source_addr, tst, sst, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_iget_nb) ( void *target_addr,
              void *source_addr,
              dmapp_seg_desc_t *source_seg,
              dmapp_pe_t source_pe,
              ptrdiff_t tst,
              ptrdiff_t sst,
              uint64_t nelems,
              dmapp_type_t type,
              dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_iget_nb) ( void *target_addr,
              void *source_addr,
              dmapp_seg_desc_t *source_seg,
              dmapp_pe_t source_pe,
              ptrdiff_t tst,
              ptrdiff_t sst,
              uint64_t nelems,
              dmapp_type_t type,
              dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_iget_nb)(target_addr, source_addr, source_seg, source_pe, tst, sst, nelems, type, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_iget_nbi) ( void *target_addr,
               void *source_addr,
               dmapp_seg_desc_t *source_seg,
               dmapp_pe_t source_pe,
               ptrdiff_t tst,
               ptrdiff_t sst,
               uint64_t nelems,
               dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_iget_nbi) ( void *target_addr,
               void *source_addr,
               dmapp_seg_desc_t *source_seg,
               dmapp_pe_t source_pe,
               ptrdiff_t tst,
               ptrdiff_t sst,
               uint64_t nelems,
               dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_iget_nbi)(target_addr, source_addr, source_seg, source_pe, tst, sst, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_iget) ( void *target_addr,
           void *source_addr,
           dmapp_seg_desc_t *source_seg,
           dmapp_pe_t source_pe,
           ptrdiff_t tst,
           ptrdiff_t sst,
           uint64_t nelems,
           dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_iget) ( void *target_addr,
           void *source_addr,
           dmapp_seg_desc_t *source_seg,
           dmapp_pe_t source_pe,
           ptrdiff_t tst,
           ptrdiff_t sst,
           uint64_t nelems,
           dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_iget)(target_addr, source_addr, source_seg, source_pe, tst, sst, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_ixput_nb) ( void *target_addr,
               dmapp_seg_desc_t *target_seg,
               dmapp_pe_t target_pe,
               void *source_addr,
               ptrdiff_t *tidx,
               uint64_t nelems,
               dmapp_type_t type,
               dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_ixput_nb) ( void *target_addr,
               dmapp_seg_desc_t *target_seg,
               dmapp_pe_t target_pe,
               void *source_addr,
               ptrdiff_t *tidx,
               uint64_t nelems,
               dmapp_type_t type,
               dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_ixput_nb)(target_addr, target_seg, target_pe, source_addr, tidx, nelems, type, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_ixput_nbi) ( void *target_addr,
                dmapp_seg_desc_t *target_seg,
                dmapp_pe_t target_pe,
                void *source_addr,
                ptrdiff_t *tidx,
                uint64_t nelems,
                dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_ixput_nbi) ( void *target_addr,
                dmapp_seg_desc_t *target_seg,
                dmapp_pe_t target_pe,
                void *source_addr,
                ptrdiff_t *tidx,
                uint64_t nelems,
                dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_ixput_nbi)(target_addr, target_seg, target_pe, source_addr, tidx, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_ixput) ( void *target_addr,
            dmapp_seg_desc_t *target_seg,
            dmapp_pe_t target_pe,
            void *source_addr,
            ptrdiff_t *tidx,
            uint64_t nelems,
            dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_ixput) ( void *target_addr,
            dmapp_seg_desc_t *target_seg,
            dmapp_pe_t target_pe,
            void *source_addr,
            ptrdiff_t *tidx,
            uint64_t nelems,
            dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_ixput)(target_addr, target_seg, target_pe, source_addr, tidx, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_ixget_nb) ( void *target_addr,
               void *source_addr,
               dmapp_seg_desc_t *source_seg,
               dmapp_pe_t source_pe,
               ptrdiff_t *sidx,
               uint64_t nelems,
               dmapp_type_t type,
               dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_ixget_nb) ( void *target_addr,
               void *source_addr,
               dmapp_seg_desc_t *source_seg,
               dmapp_pe_t source_pe,
               ptrdiff_t *sidx,
               uint64_t nelems,
               dmapp_type_t type,
               dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_ixget_nb)(target_addr, source_addr, source_seg, source_pe, sidx, nelems, type, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_ixget_nbi) ( void *target_addr,
                void *source_addr,
                dmapp_seg_desc_t *source_seg,
                dmapp_pe_t source_pe,
                ptrdiff_t *sidx,
                uint64_t nelems,
                dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_ixget_nbi) ( void *target_addr,
                void *source_addr,
                dmapp_seg_desc_t *source_seg,
                dmapp_pe_t source_pe,
                ptrdiff_t *sidx,
                uint64_t nelems,
                dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_ixget_nbi)(target_addr, source_addr, source_seg, source_pe, sidx, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_ixget) ( void *target_addr,
            void *source_addr,
            dmapp_seg_desc_t *source_seg,
            dmapp_pe_t source_pe,
            ptrdiff_t *sidx,
            uint64_t nelems,
            dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_ixget) ( void *target_addr,
            void *source_addr,
            dmapp_seg_desc_t *source_seg,
            dmapp_pe_t source_pe,
            ptrdiff_t *sidx,
            uint64_t nelems,
            dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_ixget)(target_addr, source_addr, source_seg, source_pe, sidx, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_put_ixpe_nb) ( void *target_addr,
                  dmapp_seg_desc_t *target_seg,
                  dmapp_pe_t *target_pe_list,
                  uint32_t num_target_pes,
                  void *source_addr,
                  uint64_t nelems,
                  dmapp_type_t type,
                  dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_put_ixpe_nb) ( void *target_addr,
                  dmapp_seg_desc_t *target_seg,
                  dmapp_pe_t *target_pe_list,
                  uint32_t num_target_pes,
                  void *source_addr,
                  uint64_t nelems,
                  dmapp_type_t type,
                  dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_put_ixpe_nb)(target_addr, target_seg, target_pe_list, num_target_pes, source_addr, nelems, type, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_put_ixpe_nbi) ( void *target_addr,
                   dmapp_seg_desc_t *target_seg,
                   dmapp_pe_t *target_pe_list,
                   uint32_t num_target_pes,
                   void *source_addr,
                   uint64_t nelems,
                   dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_put_ixpe_nbi) ( void *target_addr,
                   dmapp_seg_desc_t *target_seg,
                   dmapp_pe_t *target_pe_list,
                   uint32_t num_target_pes,
                   void *source_addr,
                   uint64_t nelems,
                   dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_put_ixpe_nbi)(target_addr, target_seg, target_pe_list, num_target_pes, source_addr, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_put_ixpe) ( void *target_addr,
               dmapp_seg_desc_t *target_seg,
               dmapp_pe_t *target_pe_list,
               uint32_t num_target_pes,
               void *source_addr,
               uint64_t nelems,
               dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_put_ixpe) ( void *target_addr,
               dmapp_seg_desc_t *target_seg,
               dmapp_pe_t *target_pe_list,
               uint32_t num_target_pes,
               void *source_addr,
               uint64_t nelems,
               dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_put_ixpe)(target_addr, target_seg, target_pe_list, num_target_pes, source_addr, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_scatter_ixpe_nb) ( void *target_addr,
                      dmapp_seg_desc_t *target_seg,
                      dmapp_pe_t *target_pe_list,
                      uint32_t num_target_pes,
                      void *source_addr,
                      uint64_t nelems,
                      dmapp_type_t type,
                      dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_scatter_ixpe_nb) ( void *target_addr,
                      dmapp_seg_desc_t *target_seg,
                      dmapp_pe_t *target_pe_list,
                      uint32_t num_target_pes,
                      void *source_addr,
                      uint64_t nelems,
                      dmapp_type_t type,
                      dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_scatter_ixpe_nb)(target_addr, target_seg, target_pe_list, num_target_pes, source_addr, nelems, type, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_scatter_ixpe_nbi) ( void *target_addr,
                       dmapp_seg_desc_t *target_seg,
                       dmapp_pe_t *target_pe_list,
                       uint32_t num_target_pes,
                       void *source_addr,
                       uint64_t nelems,
                       dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_scatter_ixpe_nbi) ( void *target_addr,
                       dmapp_seg_desc_t *target_seg,
                       dmapp_pe_t *target_pe_list,
                       uint32_t num_target_pes,
                       void *source_addr,
                       uint64_t nelems,
                       dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_scatter_ixpe_nbi)(target_addr, target_seg, target_pe_list, num_target_pes, source_addr, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_scatter_ixpe) ( void *target_addr,
                   dmapp_seg_desc_t *target_seg,
                   dmapp_pe_t *target_pe_list,
                   uint32_t num_target_pes,
                   void *source_addr,
                   uint64_t nelems,
                   dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_scatter_ixpe) ( void *target_addr,
                   dmapp_seg_desc_t *target_seg,
                   dmapp_pe_t *target_pe_list,
                   uint32_t num_target_pes,
                   void *source_addr,
                   uint64_t nelems,
                   dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_scatter_ixpe)(target_addr, target_seg, target_pe_list, num_target_pes, source_addr, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_gather_ixpe_nb) ( void *target_addr,
                     void *source_addr,
                     dmapp_seg_desc_t *source_seg,
                     dmapp_pe_t *source_pe_list,
                     uint32_t num_source_pes,
                     uint64_t nelems,
                     dmapp_type_t type,
                     dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_gather_ixpe_nb) ( void *target_addr,
                     void *source_addr,
                     dmapp_seg_desc_t *source_seg,
                     dmapp_pe_t *source_pe_list,
                     uint32_t num_source_pes,
                     uint64_t nelems,
                     dmapp_type_t type,
                     dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_gather_ixpe_nb)(target_addr, source_addr, source_seg, source_pe_list, num_source_pes, nelems, type, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_gather_ixpe_nbi) ( void *target_addr,
                      void *source_addr,
                      dmapp_seg_desc_t *source_seg,
                      dmapp_pe_t *source_pe_list,
                      uint32_t num_source_pes,
                      uint64_t nelems,
                      dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_gather_ixpe_nbi) ( void *target_addr,
                      void *source_addr,
                      dmapp_seg_desc_t *source_seg,
                      dmapp_pe_t *source_pe_list,
                      uint32_t num_source_pes,
                      uint64_t nelems,
                      dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_gather_ixpe_nbi)(target_addr, source_addr, source_seg, source_pe_list, num_source_pes, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_gather_ixpe) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t *source_pe_list,
                  uint32_t num_source_pes,
                  uint64_t nelems,
                  dmapp_type_t type) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_gather_ixpe) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t *source_pe_list,
                  uint32_t num_source_pes,
                  uint64_t nelems,
                  dmapp_type_t type) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_gather_ixpe)(target_addr, source_addr, source_seg, source_pe_list, num_source_pes, nelems, type);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_aadd_qw_nb) ( void *target_addr,
                 dmapp_seg_desc_t *target_seg,
                 dmapp_pe_t target_pe,
                 int64_t operand,
                 dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_aadd_qw_nb) ( void *target_addr,
                 dmapp_seg_desc_t *target_seg,
                 dmapp_pe_t target_pe,
                 int64_t operand,
                 dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_aadd_qw_nb)(target_addr, target_seg, target_pe, operand, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_aadd_qw_nbi) ( void *target_addr,
                  dmapp_seg_desc_t *target_seg,
                  dmapp_pe_t target_pe,
                  int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_aadd_qw_nbi) ( void *target_addr,
                  dmapp_seg_desc_t *target_seg,
                  dmapp_pe_t target_pe,
                  int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_aadd_qw_nbi)(target_addr, target_seg, target_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_aadd_qw) ( void *target_addr,
              dmapp_seg_desc_t *target_seg,
              dmapp_pe_t target_pe,
              int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_aadd_qw) ( void *target_addr,
              dmapp_seg_desc_t *target_seg,
              dmapp_pe_t target_pe,
              int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_aadd_qw)(target_addr, target_seg, target_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_aand_qw_nb) ( void *target_addr,
                 dmapp_seg_desc_t *target_seg,
                 dmapp_pe_t target_pe,
                 int64_t operand,
                 dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_aand_qw_nb) ( void *target_addr,
                 dmapp_seg_desc_t *target_seg,
                 dmapp_pe_t target_pe,
                 int64_t operand,
                 dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_aand_qw_nb)(target_addr, target_seg, target_pe, operand, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_aand_qw_nbi) ( void *target_addr,
                  dmapp_seg_desc_t *target_seg,
                  dmapp_pe_t target_pe,
                  int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_aand_qw_nbi) ( void *target_addr,
                  dmapp_seg_desc_t *target_seg,
                  dmapp_pe_t target_pe,
                  int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_aand_qw_nbi)(target_addr, target_seg, target_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_aand_qw) ( void *target_addr,
              dmapp_seg_desc_t *target_seg,
              dmapp_pe_t target_pe,
              int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_aand_qw) ( void *target_addr,
              dmapp_seg_desc_t *target_seg,
              dmapp_pe_t target_pe,
              int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_aand_qw)(target_addr, target_seg, target_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_aor_qw_nb) ( void *target_addr,
                dmapp_seg_desc_t *target_seg,
                dmapp_pe_t target_pe,
                int64_t operand,
                dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_aor_qw_nb) ( void *target_addr,
                dmapp_seg_desc_t *target_seg,
                dmapp_pe_t target_pe,
                int64_t operand,
                dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_aor_qw_nb)(target_addr, target_seg, target_pe, operand, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_aor_qw_nbi) ( void *target_addr,
                 dmapp_seg_desc_t *target_seg,
                 dmapp_pe_t target_pe,
                 int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_aor_qw_nbi) ( void *target_addr,
                 dmapp_seg_desc_t *target_seg,
                 dmapp_pe_t target_pe,
                 int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_aor_qw_nbi)(target_addr, target_seg, target_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_aor_qw) ( void *target_addr,
             dmapp_seg_desc_t *target_seg,
             dmapp_pe_t target_pe,
             int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_aor_qw) ( void *target_addr,
             dmapp_seg_desc_t *target_seg,
             dmapp_pe_t target_pe,
             int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_aor_qw)(target_addr, target_seg, target_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_axor_qw_nb) ( void *target_addr,
                 dmapp_seg_desc_t *target_seg,
                 dmapp_pe_t target_pe,
                 int64_t operand,
                 dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_axor_qw_nb) ( void *target_addr,
                 dmapp_seg_desc_t *target_seg,
                 dmapp_pe_t target_pe,
                 int64_t operand,
                 dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_axor_qw_nb)(target_addr, target_seg, target_pe, operand, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_axor_qw_nbi) ( void *target_addr,
                  dmapp_seg_desc_t *target_seg,
                  dmapp_pe_t target_pe,
                  int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_axor_qw_nbi) ( void *target_addr,
                  dmapp_seg_desc_t *target_seg,
                  dmapp_pe_t target_pe,
                  int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_axor_qw_nbi)(target_addr, target_seg, target_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_axor_qw) ( void *target_addr,
              dmapp_seg_desc_t *target_seg,
              dmapp_pe_t target_pe,
              int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_axor_qw) ( void *target_addr,
              dmapp_seg_desc_t *target_seg,
              dmapp_pe_t target_pe,
              int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_axor_qw)(target_addr, target_seg, target_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afadd_qw_nb) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t source_pe,
                  int64_t operand,
                  dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afadd_qw_nb) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t source_pe,
                  int64_t operand,
                  dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afadd_qw_nb)(target_addr, source_addr, source_seg, source_pe, operand, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afadd_qw_nbi) ( void *target_addr,
                   void *source_addr,
                   dmapp_seg_desc_t *source_seg,
                   dmapp_pe_t source_pe,
                   int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afadd_qw_nbi) ( void *target_addr,
                   void *source_addr,
                   dmapp_seg_desc_t *source_seg,
                   dmapp_pe_t source_pe,
                   int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afadd_qw_nbi)(target_addr, source_addr, source_seg, source_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afadd_qw) ( void *target_addr,
               void *source_addr,
               dmapp_seg_desc_t *source_seg,
               dmapp_pe_t source_pe,
               int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afadd_qw) ( void *target_addr,
               void *source_addr,
               dmapp_seg_desc_t *source_seg,
               dmapp_pe_t source_pe,
               int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afadd_qw)(target_addr, source_addr, source_seg, source_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afand_qw_nb) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t source_pe,
                  int64_t operand,
                  dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afand_qw_nb) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t source_pe,
                  int64_t operand,
                  dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afand_qw_nb)(target_addr, source_addr, source_seg, source_pe, operand, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afand_qw_nbi) ( void *target_addr,
                   void *source_addr,
                   dmapp_seg_desc_t *source_seg,
                   dmapp_pe_t source_pe,
                   int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afand_qw_nbi) ( void *target_addr,
                   void *source_addr,
                   dmapp_seg_desc_t *source_seg,
                   dmapp_pe_t source_pe,
                   int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afand_qw_nbi)(target_addr, source_addr, source_seg, source_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afand_qw) ( void *target_addr,
               void *source_addr,
               dmapp_seg_desc_t *source_seg,
               dmapp_pe_t source_pe,
               int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afand_qw) ( void *target_addr,
               void *source_addr,
               dmapp_seg_desc_t *source_seg,
               dmapp_pe_t source_pe,
               int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afand_qw)(target_addr, source_addr, source_seg, source_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afxor_qw_nb) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t source_pe,
                  int64_t operand,
                  dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afxor_qw_nb) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t source_pe,
                  int64_t operand,
                  dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afxor_qw_nb)(target_addr, source_addr, source_seg, source_pe, operand, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afxor_qw_nbi) ( void *target_addr,
                   void *source_addr,
                   dmapp_seg_desc_t *source_seg,
                   dmapp_pe_t source_pe,
                   int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afxor_qw_nbi) ( void *target_addr,
                   void *source_addr,
                   dmapp_seg_desc_t *source_seg,
                   dmapp_pe_t source_pe,
                   int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afxor_qw_nbi)(target_addr, source_addr, source_seg, source_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afxor_qw) ( void *target_addr,
               void *source_addr,
               dmapp_seg_desc_t *source_seg,
               dmapp_pe_t source_pe,
               int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afxor_qw) ( void *target_addr,
               void *source_addr,
               dmapp_seg_desc_t *source_seg,
               dmapp_pe_t source_pe,
               int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afxor_qw)(target_addr, source_addr, source_seg, source_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afor_qw_nb) ( void *target_addr,
                 void *source_addr,
                 dmapp_seg_desc_t *source_seg,
                 dmapp_pe_t source_pe,
                 int64_t operand,
                 dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afor_qw_nb) ( void *target_addr,
                 void *source_addr,
                 dmapp_seg_desc_t *source_seg,
                 dmapp_pe_t source_pe,
                 int64_t operand,
                 dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afor_qw_nb)(target_addr, source_addr, source_seg, source_pe, operand, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afor_qw_nbi) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t source_pe,
                  int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afor_qw_nbi) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t source_pe,
                  int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afor_qw_nbi)(target_addr, source_addr, source_seg, source_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afor_qw) ( void *target_addr,
              void *source_addr,
              dmapp_seg_desc_t *source_seg,
              dmapp_pe_t source_pe,
              int64_t operand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afor_qw) ( void *target_addr,
              void *source_addr,
              dmapp_seg_desc_t *source_seg,
              dmapp_pe_t source_pe,
              int64_t operand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afor_qw)(target_addr, source_addr, source_seg, source_pe, operand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afax_qw_nb) ( void *target_addr,
                 void *source_addr,
                 dmapp_seg_desc_t *source_seg,
                 dmapp_pe_t source_pe,
                 int64_t andMask,
                 int64_t xorMask,
                 dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afax_qw_nb) ( void *target_addr,
                 void *source_addr,
                 dmapp_seg_desc_t *source_seg,
                 dmapp_pe_t source_pe,
                 int64_t andMask,
                 int64_t xorMask,
                 dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afax_qw_nb)(target_addr, source_addr, source_seg, source_pe, andMask, xorMask, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afax_qw_nbi) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t source_pe,
                  int64_t andMask,
                  int64_t xorMask) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afax_qw_nbi) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t source_pe,
                  int64_t andMask,
                  int64_t xorMask) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afax_qw_nbi)(target_addr, source_addr, source_seg, source_pe, andMask, xorMask);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_afax_qw) ( void *target_addr,
              void *source_addr,
              dmapp_seg_desc_t *source_seg,
              dmapp_pe_t source_pe,
              int64_t andMask,
              int64_t xorMask) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_afax_qw) ( void *target_addr,
              void *source_addr,
              dmapp_seg_desc_t *source_seg,
              dmapp_pe_t source_pe,
              int64_t andMask,
              int64_t xorMask) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_afax_qw)(target_addr, source_addr, source_seg, source_pe, andMask, xorMask);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_acswap_qw_nb) ( void *target_addr,
                   void *source_addr,
                   dmapp_seg_desc_t *source_seg,
                   dmapp_pe_t source_pe,
                   int64_t comperand,
                   int64_t swaperand,
                   dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_acswap_qw_nb) ( void *target_addr,
                   void *source_addr,
                   dmapp_seg_desc_t *source_seg,
                   dmapp_pe_t source_pe,
                   int64_t comperand,
                   int64_t swaperand,
                   dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_acswap_qw_nb)(target_addr, source_addr, source_seg, source_pe, comperand, swaperand, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_acswap_qw_nbi) ( void *target_addr,
                    void *source_addr,
                    dmapp_seg_desc_t *source_seg,
                    dmapp_pe_t source_pe,
                    int64_t comperand,
                    int64_t swaperand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_acswap_qw_nbi) ( void *target_addr,
                    void *source_addr,
                    dmapp_seg_desc_t *source_seg,
                    dmapp_pe_t source_pe,
                    int64_t comperand,
                    int64_t swaperand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_acswap_qw_nbi)(target_addr, source_addr, source_seg, source_pe, comperand, swaperand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_acswap_qw) ( void *target_addr,
                void *source_addr,
                dmapp_seg_desc_t *source_seg,
                dmapp_pe_t source_pe,
                int64_t comperand,
                int64_t swaperand) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_acswap_qw) ( void *target_addr,
                void *source_addr,
                dmapp_seg_desc_t *source_seg,
                dmapp_pe_t source_pe,
                int64_t comperand,
                int64_t swaperand) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_acswap_qw)(target_addr, source_addr, source_seg, source_pe, comperand, swaperand);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_lock_acquire) ( dmapp_lock_desc_t *lock_addr,
     dmapp_seg_desc_t *lock_seg,
     dmapp_pe_t lock_host,
     uint64_t flags,
                   dmapp_lock_handle_t *handle) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_lock_acquire) ( dmapp_lock_desc_t *lock_addr,
     dmapp_seg_desc_t *lock_seg,
     dmapp_pe_t lock_host,
     uint64_t flags,
                   dmapp_lock_handle_t *handle) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_lock_acquire)(lock_addr, lock_seg, lock_host, flags, handle);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_lock_try) ( dmapp_lock_desc_t *lock_addr,
               dmapp_seg_desc_t *lock_seg,
               dmapp_pe_t lock_host,
               uint64_t flags,
               dmapp_lock_handle_t *handle) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_lock_try) ( dmapp_lock_desc_t *lock_addr,
               dmapp_seg_desc_t *lock_seg,
               dmapp_pe_t lock_host,
               uint64_t flags,
               dmapp_lock_handle_t *handle) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_lock_try)(lock_addr, lock_seg, lock_host, flags, handle);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_lock_release) ( dmapp_lock_handle_t handle,
     uint64_t flags) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_lock_release) ( dmapp_lock_handle_t handle,
     uint64_t flags) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_lock_release)(handle, flags);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_lock_release_addr) ( dmapp_lock_desc_t *lock_addr,
                        dmapp_pe_t lock_host,
                        uint64_t flags) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_lock_release_addr) ( dmapp_lock_desc_t *lock_addr,
                        dmapp_pe_t lock_host,
                        uint64_t flags) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_lock_release_addr)(lock_addr, lock_host, flags);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_sheap_stats) (dmapp_sheap_stats_t *stats) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_sheap_stats) (dmapp_sheap_stats_t *stats) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_sheap_stats)(stats);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_mem_register) ( void *addr,
                   uint64_t length,
                   dmapp_seg_desc_t *seg_desc) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_mem_register) ( void *addr,
                   uint64_t length,
                   dmapp_seg_desc_t *seg_desc) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_mem_register)(addr, length, seg_desc);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_mem_unregister) ( dmapp_seg_desc_t *seg_desc) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_mem_unregister) ( dmapp_seg_desc_t *seg_desc) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_mem_unregister)(seg_desc);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_segdesc_compare) ( dmapp_seg_desc_t *seg_desc1,
                      dmapp_seg_desc_t *seg_desc2,
                      int *flag) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_segdesc_compare) ( dmapp_seg_desc_t *seg_desc1,
                      dmapp_seg_desc_t *seg_desc2,
                      int *flag) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_segdesc_compare)(seg_desc1, seg_desc2, flag);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_mem_reserve) ( void *addr,
                  uint64_t length,
                  uint64_t flags,
                  dmapp_seg_desc_t *seg_desc) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_mem_reserve) ( void *addr,
                  uint64_t length,
                  uint64_t flags,
                  dmapp_seg_desc_t *seg_desc) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_mem_reserve)(addr, length, flags, seg_desc);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_mem_update) ( void *addr,
                 uint64_t length,
                 uint64_t flags,
                 dmapp_seg_desc_t *seg_desc) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_mem_update) ( void *addr,
                 uint64_t length,
                 uint64_t flags,
                 dmapp_seg_desc_t *seg_desc) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_mem_update)(addr, length, flags, seg_desc);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_checkpoint) (void) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_checkpoint) (void) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_checkpoint)();
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_restart) ( uint32_t restart_modes) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_restart) ( uint32_t restart_modes) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_restart)(restart_modes);
}
extern dmapp_return_t  REAL_FUNCTION(dmapp_progress) (void) ;
dmapp_return_t  WRAPPED_FUNCTION(dmapp_progress) (void) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_progress)();
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_c_pset_create) ( dmapp_c_pset_desc_t *pdesc,
                    uint64_t identifier,
                    uint64_t modes,
                    dmapp_c_pset_attrs_t *attrs,
                    dmapp_c_pset_handle_t *pset_hndl) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_c_pset_create) ( dmapp_c_pset_desc_t *pdesc,
                    uint64_t identifier,
                    uint64_t modes,
                    dmapp_c_pset_attrs_t *attrs,
                    dmapp_c_pset_handle_t *pset_hndl) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_c_pset_create)(pdesc, identifier, modes, attrs, pset_hndl);
}
extern dmapp_return_t  REAL_FUNCTION(dmapp_c_pset_export) ( dmapp_c_pset_handle_t pset_hndl) ;
dmapp_return_t  WRAPPED_FUNCTION(dmapp_c_pset_export) ( dmapp_c_pset_handle_t pset_hndl) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_c_pset_export)(pset_hndl);
}
extern dmapp_return_t  REAL_FUNCTION(dmapp_c_pset_destroy) ( dmapp_c_pset_handle_t pset_hndl) ;
dmapp_return_t  WRAPPED_FUNCTION(dmapp_c_pset_destroy) ( dmapp_c_pset_handle_t pset_hndl) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_c_pset_destroy)(pset_hndl);
}
extern dmapp_return_t  REAL_FUNCTION(dmapp_c_barrier_join) ( dmapp_c_pset_handle_t pset_hndl) ;
dmapp_return_t  WRAPPED_FUNCTION(dmapp_c_barrier_join) ( dmapp_c_pset_handle_t pset_hndl) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_c_barrier_join)(pset_hndl);
}
extern dmapp_return_t  REAL_FUNCTION(dmapp_c_greduce_start) ( dmapp_c_pset_handle_t pset,
                                            void *in,
                                            void *out,
                                            uint32_t nelems,
                                            dmapp_c_type_t type,
                                            dmapp_c_op_t op) ;
dmapp_return_t  WRAPPED_FUNCTION(dmapp_c_greduce_start) ( dmapp_c_pset_handle_t pset,
                                            void *in,
                                            void *out,
                                            uint32_t nelems,
                                            dmapp_c_type_t type,
                                            dmapp_c_op_t op) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_c_greduce_start)(pset, in, out, nelems, type, op);
}
extern dmapp_return_t  REAL_FUNCTION(dmapp_c_greduce_nelems_max) ( dmapp_c_type_t type,
                                                 uint32_t *nelems_max) ;
dmapp_return_t  WRAPPED_FUNCTION(dmapp_c_greduce_nelems_max) ( dmapp_c_type_t type,
                                                 uint32_t *nelems_max) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_c_greduce_nelems_max)(type, nelems_max);
}
extern dmapp_return_t  REAL_FUNCTION(dmapp_c_pset_test) ( dmapp_c_pset_handle_t pset_hndl) ;
dmapp_return_t  WRAPPED_FUNCTION(dmapp_c_pset_test) ( dmapp_c_pset_handle_t pset_hndl) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_c_pset_test)(pset_hndl);
}
extern dmapp_return_t  REAL_FUNCTION(dmapp_c_pset_wait) ( dmapp_c_pset_handle_t pset_hndl) ;
dmapp_return_t  WRAPPED_FUNCTION(dmapp_c_pset_wait) ( dmapp_c_pset_handle_t pset_hndl) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_c_pset_wait)(pset_hndl);
}
extern dmapp_return_t  REAL_FUNCTION(dmapp_c_pset_cancel_op) ( dmapp_c_pset_handle_t pset_hndl) ;
dmapp_return_t  WRAPPED_FUNCTION(dmapp_c_pset_cancel_op) ( dmapp_c_pset_handle_t pset_hndl) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_c_pset_cancel_op)(pset_hndl);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_amo_put) ( void *target_addr,
              dmapp_seg_desc_t *target_seg,
              dmapp_pe_t target_pe,
              dmapp_amo_t *amo) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_amo_put) ( void *target_addr,
              dmapp_seg_desc_t *target_seg,
              dmapp_pe_t target_pe,
              dmapp_amo_t *amo) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_amo_put)(target_addr, target_seg, target_pe, amo);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_amo_put_nb) ( void *target_addr,
                 dmapp_seg_desc_t *target_seg,
                 dmapp_pe_t target_pe,
                 dmapp_amo_t *amo,
                 dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_amo_put_nb) ( void *target_addr,
                 dmapp_seg_desc_t *target_seg,
                 dmapp_pe_t target_pe,
                 dmapp_amo_t *amo,
                 dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_amo_put_nb)(target_addr, target_seg, target_pe, amo, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_amo_put_nbi) ( void *target_addr,
                  dmapp_seg_desc_t *target_seg,
                  dmapp_pe_t target_pe,
                  dmapp_amo_t *amo) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_amo_put_nbi) ( void *target_addr,
                  dmapp_seg_desc_t *target_seg,
                  dmapp_pe_t target_pe,
                  dmapp_amo_t *amo) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_amo_put_nbi)(target_addr, target_seg, target_pe, amo);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_amo_get) ( void *target_addr,
              void *source_addr,
              dmapp_seg_desc_t *source_seg,
              dmapp_pe_t source_pe,
              dmapp_amo_t *amo) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_amo_get) ( void *target_addr,
              void *source_addr,
              dmapp_seg_desc_t *source_seg,
              dmapp_pe_t source_pe,
              dmapp_amo_t *amo) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_amo_get)(target_addr, source_addr, source_seg, source_pe, amo);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_amo_get_nb) ( void *target_addr,
                 void *source_addr,
                 dmapp_seg_desc_t *source_seg,
                 dmapp_pe_t source_pe,
                 dmapp_amo_t *amo,
                 dmapp_syncid_handle_t *syncid) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_amo_get_nb) ( void *target_addr,
                 void *source_addr,
                 dmapp_seg_desc_t *source_seg,
                 dmapp_pe_t source_pe,
                 dmapp_amo_t *amo,
                 dmapp_syncid_handle_t *syncid) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_amo_get_nb)(target_addr, source_addr, source_seg, source_pe, amo, syncid);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_amo_get_nbi) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t source_pe,
                  dmapp_amo_t *amo) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_amo_get_nbi) ( void *target_addr,
                  void *source_addr,
                  dmapp_seg_desc_t *source_seg,
                  dmapp_pe_t source_pe,
                  dmapp_amo_t *amo) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_amo_get_nbi)(target_addr, source_addr, source_seg, source_pe, amo);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_amo_flush) ( dmapp_pe_t target_pe, uint64_t flags) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_amo_flush) ( dmapp_pe_t target_pe, uint64_t flags) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_amo_flush)(target_pe, flags);
}
extern dmapp_return_t
 REAL_FUNCTION(dmapp_queue_put) ( dmapp_queue_handle_t queue_hndl,
  void *source,
  uint64_t nelems,
  dmapp_type_t type,
  dmapp_pe_t target_pe,
  uint64_t flags) ;
dmapp_return_t
 WRAPPED_FUNCTION(dmapp_queue_put) ( dmapp_queue_handle_t queue_hndl,
  void *source,
  uint64_t nelems,
  dmapp_type_t type,
  dmapp_pe_t target_pe,
  uint64_t flags) {
	 gAccessedRemoteData = true;
	 return REAL_FUNCTION(dmapp_queue_put)(queue_hndl, source, nelems, type, target_pe, flags);
}
}
