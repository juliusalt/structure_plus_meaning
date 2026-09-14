theory Factor_Package_Scope_Identity
  imports Factor_Package_Dependencies
begin

theorem native_package_same_scope:
  assumes first: "native_package_at E u r P" and second: "native_package_at F u r Q"
    and same: "native_package_environment E u r=native_package_environment F u r"
  shows "P=Q"
proof -
  have left: "native_package_at (native_package_environment E u r) u r P"
    by (rule native_package_environment_recovers[OF first])
  have right: "native_package_at (native_package_environment E u r) u r Q"
    using native_package_environment_recovers[OF second] by (simp only: same)
  show ?thesis by (rule native_package_unique[OF left right])
qed

end
