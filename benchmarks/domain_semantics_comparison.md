# Domain semantics: vocabulary versus responsibility

An early version grouped symbols by frequent concept tokens. On business code,
those words often coincided with useful domains. On a technical service, it
produced buckets such as `Prefix`, `Setup`, and `Graph`: vocabulary rather than
architectural responsibility.

The replacement, domains-v3, uses dependency communities and directory-derived
units to determine membership. An optional, separate `enrich` build can name
those communities with a model; it cannot change their membership.

The public evaluation uses the pinned cohort in `cohort.json` and the reviewed
eShop decomposition in `ground_truth/eshop_domains.json`. Structural checks
catch collapse and fragmentation; semantic alignment checks whether the groups
match that decomposition. A single semantic fixture does not establish
correct domain recovery for arbitrary repositories.
