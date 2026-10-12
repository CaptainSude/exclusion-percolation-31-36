# Publish this project on GitHub

[Back to the project README](../README.md)

Use GitHub Desktop to upload the complete project. This package has 443 Lean source files; GitHub's browser uploader allows only 100 files at a time. [Official upload limits](https://docs.github.com/en/repositories/working-with-files/managing-files/adding-a-file-to-a-repository)

1. **Extract the package**, if you downloaded it as a ZIP. Open the extracted `exclusion-percolation-31-36` folder and confirm that it contains `README.md`, `ExceptionalTimes`, `paper`, and `verification`.

2. **Install [GitHub Desktop](https://desktop.github.com/) and sign in.** On Windows, use **File → Options → Accounts → Sign Into GitHub.com**. [Official setup guide](https://docs.github.com/en/desktop/overview/getting-started-with-github-desktop)

3. **Create a new local repository in a different folder.** In Desktop, choose **File → New repository…**. Enter `exclusion-percolation-31-36` as the name. For the local path, choose another parent folder, such as `Documents/GitHub`; Desktop creates the repository folder inside it. Leave the extra initialization options off: this package already includes its README and ignore settings. Click **Create repository**. [Official creation guide](https://docs.github.com/en/desktop/overview/creating-your-first-repository-using-github-desktop)

4. **Copy the prepared contents into the new repository.** In your file manager, copy everything *inside* the extracted project folder into the folder Desktop just created. Include `.github`, `.vscode`, `.gitattributes`, and `.gitignore`; enable hidden-file display if necessary. Copy the contents, not the enclosing folder or ZIP. The README, Lean files, `paper`, and `verification` should be directly inside the new repository. If prompted about `.gitattributes`, use the copy from the prepared package.

5. **Save the initial commit.** Return to Desktop's **Changes** tab. Keep all project files selected, enter `Initial public release` in **Summary**, and click **Commit to main**. The button displays your actual branch name.

6. **Publish the public repository.** Click **Publish repository**, confirm the name, and clear **Keep this code private**. If an organization selector appears, choose **None** for your personal account. Click **Publish Repository**. [Official publishing instructions](https://docs.github.com/en/desktop/adding-and-cloning-repositories/adding-an-existing-project-to-github-using-github-desktop)

7. **Check the published files.** Choose **Repository → View on GitHub**. Confirm that the README is displayed and its paper and proof links open.

8. **Create the release tag.** On GitHub, open **Releases → Draft a new release**. Under **Choose a tag**, type `v1.0.0` and select **Create new tag**. Set **Target** to the branch you published, normally `main`. [Official release guide](https://docs.github.com/en/repositories/releasing-projects-on-github/managing-releases-in-a-repository)

9. **Add the release text and files.** Use `v1.0.0 — Paper and Lean verification` as the title. Copy the body of [the prepared release notes](release-notes.md) into **Describe this release**. Attach these two files from your project folder:

   - [`paper/nearest-neighbor-31-36.pdf`](../paper/nearest-neighbor-31-36.pdf)
   - [`verification/nearest-neighbor-31-36-lean.zip`](../verification/nearest-neighbor-31-36-lean.zip), the preserved standalone Lean archive

10. **Publish the release.** Wait for both attachments to finish uploading, then click **Publish release**. Share the resulting release-page link.

For later changes, commit the updated files in Desktop and click **Push origin**.
