#include <chrono>
#include <lean/lean.h>

extern "C" LEAN_EXPORT lean_obj_res lean_get_current_time() {
    using namespace std::chrono;

    steady_clock::time_point now = steady_clock::now();
    steady_clock::duration duration = now.time_since_epoch();

    long long secs = duration_cast<seconds>(duration).count();
    long long nano = duration_cast<nanoseconds>(duration).count() % 1000000000;

    lean_object *lean_ts = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(lean_ts, 0, lean_int_to_int(static_cast<int>(secs)));
    lean_ctor_set(lean_ts, 1, lean_int_to_int(static_cast<int>(nano)));

    return lean_io_result_mk_ok(lean_ts);
}

extern "C" LEAN_EXPORT lean_obj_res lean_get_current_timestamp() {
    using namespace std::chrono;

    system_clock::time_point now = system_clock::now();
    long long timestamp = duration_cast<seconds>(now.time_since_epoch()).count();

    lean_object *lean_timestamp = lean_int_to_int((int)timestamp);
    return lean_io_result_mk_ok(lean_timestamp);
}