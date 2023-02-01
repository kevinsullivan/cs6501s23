# Upload

- pushd build/html
- aws s3 cp ./ s3://website-computingfoundations-org-prod-site --recursive
- aws cloudfront create-invalidation --distribution-id E2YE3KBBR5M5DS --paths "/*"
- popd