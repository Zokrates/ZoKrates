#!/usr/bin/env groovy

def version

pipeline {
    agent any
    stages {
        stage('Init') {
            steps {
                script {
                    def gitCommitHash = sh(returnStdout: true, script: 'git rev-parse HEAD').trim().take(7)
                    currentBuild.displayName = "#${BUILD_ID}-${gitCommitHash}"

                    version = sh(returnStdout: true, script: 'cat Cargo.toml | grep version | awk \'{print $3}\' | sed -e \'s/"//g\'').trim()
                    echo "ZoKrates Version: ${version}"
                }
            }
        }
        stage('Build') {
            steps {
                withDockerContainer('kyroy/zokrates-test') {
                    sh 'RUSTFLAGS="-D warnings" cargo build'
                }
            }
        }

        stage('Test') {
            steps {
                withDockerContainer('kyroy/zokrates-test') {
                    sh 'RUSTFLAGS="-D warnings" cargo test'
                }
            }
        }

        stage('Integration Test') {
            when {
                expression { env.BRANCH_NAME == 'master' || env.BRANCH_NAME == 'develop' }
            }
            steps {
                withDockerContainer('kyroy/zokrates-test') {
                    sh 'RUSTFLAGS="-D warnings" cargo test -- --ignored'
                }
            }
        }

        stage('Docker Build & Push') {
            when {
                expression { env.BRANCH_NAME == 'master' }
            }
            steps {
                script {
                    def dockerImage = docker.build("kyroy/zokrates")
                    docker.withRegistry('https://registry.hub.docker.com', 'dockerhub-kyroy') {
                        dockerImage.push(version)
                        dockerImage.push("latest")
                    }
                }
            }
        }
    }
    post {
        always {
            // junit allowEmptyResults: true, testResults: '*test.xml'
            deleteDir()
        }
        changed {
            notifyStatusChange notificationRecipients: 'mail@kyroy.com', componentName: 'ZoKrates'
        }
    }
}
